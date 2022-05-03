from setuptools.command.sdist import sdist as SDistOriginal
from distutils.command.build import build as BuildOriginal  # TODO
from setuptools import setup, Command
from multiprocessing import cpu_count
from contextlib import contextmanager
from hashlib import sha256
from enum import Enum
from tqdm import tqdm
from glob import glob
import subprocess
import requests
import platform
import tempfile
import string
import shutil
import sys
import os
import re

# Shared libraries
import z3


# TODO: pycache is not excluded?
# TODO: I think our sdists are GPL3?


######################################################################
#                              Globals                               #
######################################################################


# Paths
claripy = os.path.dirname(os.path.abspath(__file__))
native = os.path.join(claripy, "native")

with open(os.path.join(claripy, "VERSION")) as f:
    version = f.read().strip()

# Claricpp library names; these should be in MANIFEST.in
claricpp = "claricpp"


######################################################################
#                              Helpers                               #
######################################################################


class JDict(dict):
    """
    A key-read-only dict that allows . semantics
    """

    __getattr__ = dict.get
    __setattr__ = None
    __delattr__ = None


@contextmanager
def chdir(new):
    """
    Current working directory context manager
    """
    old = os.getcwd()
    new = os.path.abspath(new)
    try:
        print("cd " + new)
        os.chdir(new)
        yield
    finally:
        print("cd " + old)
        os.chdir(old)


def find_exe(name, fail_ok=False):
    """
    Akin to bash's which function
    """
    exe = shutil.which(name, mode=os.X_OK)
    if exe is None and not fail_ok:
        raise RuntimeError("Cannot find " + name)
    return exe


def cname(x):
    """
    Return the class name of x
    """
    return x.__class__.__name__


class BuiltLib:
    """
    A shared or static library
    """

    install_dir = os.path.join(claripy, "claripy/native")

    def __init__(self, name, build_dir, *, permit_shared, permit_static):
        self.name = name
        self._lic = os.path.join(self.install_dir, "LICENSE." + name.replace(" ", "_"))
        self.build_dir = build_dir
        # Determine extensions
        self._permit_shared = permit_shared
        self._permit_static = permit_static
        self._licensed = False

    def init_license(self, installer, cleaner):
        """
        Install license handling functions
        """
        self._lic_installer = installer
        self._lic_cleaner = cleaner

    def _find_ext(self, where, ext):
        exact = os.path.realpath(os.path.join(where, self.name + ext))
        if os.path.exists(exact):
            return exact
        files = glob(os.path.join(where, self.name) + ".*")
        # Check ext after glob b/c .'s can overlap
        files = [i for i in files if i.endswith(ext)]
        if len(files) == 1:
            return files[0]
        if len(files) > 1:
            print("Found: " + str(files))
            raise RuntimeError(
                "Multiple "
                + self.name
                + " libraries in "
                + where
                + " with the same extension: "
                + ext
                + ": "
                + str(files)
            )

    def _find(self, where):
        """
        Tries to find a library within the directory where
        Will prefer the native file extension type but may permit others
        Static libraries have the lowest preference
        """
        exts = []
        if self._permit_shared:
            ops = platform.system()
            if ops == "Darwin":
                exts.extend([".dylib", ".so"])
            elif ops == "Windows":
                exts.extend([".dll", ".so"])
            else:
                exts.extend([".so", ".dll", ".dylib"])
        if self._permit_static:
            exts.append(".a")
        found = [self._find_ext(where, i) for i in exts]
        found = [i for i in found if i is not None] + [None]
        return found[0]

    def find_installed(self):
        """
        Look for the library in the installation directory
        """
        return self._find(self.install_dir)

    def find_built(self):
        """
        Look for the library in the build directory
        """
        return self._find(self.build_dir)

    def licensed(self, b):
        self._licensed = b

    def install(self):
        """
        Copies the library from build dir to install dir
        """
        assert self._licensed is not None, "Will not install without a license"
        p = self.find_built()
        assert p is not None, "Cannot install a non-built library"
        shutil.copy2(p, self.install_dir)

    def _clean(self, x):
        if x:
            os.remove(x)

    def clean_build(self):
        self._clean(self.find_built())

    def clean_install(self):
        self._clean(self.find_installed())


class SharedLib(BuiltLib):
    """
    A shared library
    """

    def __init__(self, name: str, build_dir: str):
        super().__init__(name, build_dir, permit_shared=True, permit_static=False)


class StaticLib(BuiltLib):
    """
    A shared library
    """

    def __init__(self, name: str, build_dir: str):
        super().__init__(name, build_dir, permit_shared=False, permit_static=True)


def run_cmd_no_fail(*args, **kwargs):
    """
    A wrapper around subprocess.run that errors on subprocess failure
    Returns subprocess.run(args, **kwargs
    """
    args = list(args)
    print("Running command: " + str(args))
    rc = subprocess.run(args, **kwargs)
    if rc.returncode != 0:
        if rc.stdout:
            print(rc.stdout)
        if rc.stderr:
            print(rc.stderr, file=sys.stderr)
        what = os.path.basename(args[0])
        raise RuntimeError(what + " failed with return code: " + str(rc.returncode))
    return rc


def extract(d, f, ext):
    """
    Extract f into d given, the compression is assumed from the extension (ext)
    No leading period is allowed in ext
    """
    if ".tar" in ext:
        import tarfile

        with tarfile.open(f) as z:
            z.extractall(d)
    elif ext == "zip":
        from zipfile import ZipFile

        with ZipFile(f) as z:
            z.extractall(d)
    else:
        raise RuntimeError("Compression type not supported: " + ext)


def build_cmake_target(target, *args):
    """
    Build the target with multiple jobs
    Extra args may be passed to the generator via args
    Run this from the same directory you would the generator
    """
    cmake = [find_exe("cmake"), "--build", "."]
    j = "-j" + str(max(cpu_count() - 1, 1))
    return run_cmd_no_fail(*cmake, j, "--target", target, "--", *args)


def download_checksum_extract(name, where, url, sha, ext):
    """
    Download a file from url, checksum it, then extract it into a temp dir
    Return the temp dir and the files within it
    """
    print("Downloading and hash-verifying " + name + "...")
    hasher = sha256()
    prefix = re.sub(r"\s+", "_", name) + "-"
    fd, comp_f = tempfile.mkstemp(dir=where, prefix=prefix, suffix=ext)
    with os.fdopen(fd, "wb") as f:
        with requests.get(url, allow_redirects=True, stream=True) as r:
            r.raise_for_status()
            as_bytes = {"unit": "B", "unit_scale": True, "unit_divisor": 1024}
            with tqdm(total=int(r.headers["Content-length"]), **as_bytes) as prog:
                chunk_size = 2**16
                for block in r.iter_content(chunk_size=chunk_size):
                    hasher.update(block)
                    f.write(block)
                    prog.update(chunk_size)
    if hasher.hexdigest() != sha:
        raise RuntimeError("Downloaded " + name + " hash failure!")
    # Extract
    raw = tempfile.mkdtemp(dir=where, prefix=prefix + "dir-", suffix=".tmp")
    print("Extracting " + name + " to: " + raw)
    extract(raw, comp_f, ext)
    os.remove(comp_f)
    return raw, glob(os.path.join(raw, "*"))


class CleanLevel(Enum):
    """
    Higher clean levels imply lower clean levels
    Values will be incremented by 1 between levels
    Non-whole values are allowed but may only be referenced in clean functions
    """

    INSTALL = 1
    LICENSE = 2
    BUILT_LIBS = 2.5
    BUILD = 3
    BUILD_DEPS = 3.5
    GET = 4


# 'Member functions' of CleanLevel
setattr(type(CleanLevel.GET), "implies", lambda self, o: self.value >= o.value)
setattr(type(CleanLevel.GET), "inc", lambda self: CleanLevel(self.value + 1))


def to_clean_lvl(name):
    """
    Get the clean level named name
    """
    name = name.upper()
    try:
        return getattr(CleanLevel, name)
    except AttributeError:
        valid = [i.name for i in CleanLevel]
        valid = "Valid clean levels: " + ", ".join(valid)
        msg = "Invalid clean level: " + name + ". " + valid
        raise Exception(msg)


######################################################################
#                         Dependency Classes                         #
######################################################################


class Library:
    """
    Native dependencies should derive from this
    Subclasses may want to override _get, _build, _install, and _clean
    """

    def __init__(self, get_chk, build_chk, install_chk, *dependencies):
        """
        get_chk, build_chk, and install_chk are dicts to given to _body
        When call .get(), self._done(*i) will be called for i in get_chk
        If all return true, the get stage will be skipped
        Likewise this is true for build_chk/install_chk stages build/install
        Note: If any values in the chk dicts are BuiltLibs, they will be swapped
        for the the .find_built / .find_installed functions as needed
        Subclasses must override _license
        Will only call _get, _build, _license, and _install once
        """
        self._done_set = set()
        self._dependencies = dependencies
        assert self._dep_check(type(self)), "Cyclical dependency found on: " + str(
            type(self)
        )
        # Done check lists
        self._get_chk = dict(get_chk)
        self._build_chk = self._fix_chk(build_chk, "find_built")
        self._install_chk = self._fix_chk(install_chk, "find_installed")

    @staticmethod
    def _fix_chk(d, name):
        """
        Update replace BuiltLib values in d with their name functions
        """
        fix = lambda x: getattr(x, name) if isinstance(x, BuiltLib) else x
        return {i: fix(k) for i, k in d.items()}

    def _dep_check(self, t):
        """
        Return true iff t is not a dependency recursively
        """
        return all([(type(i) != t and i._dep_check(t)) for i in self._dependencies])

    def _done(self, name, path):
        """
        If path is a function, path = path()
        If path exists, note it will be reused and return True
        This will only warn once per path!
        path may be None
        """
        if callable(path):
            path = path()
        ret = False if path is None else os.path.exists(path)
        if path in self._done_set:
            assert ret, path + " used to exist but now does not"
        elif ret:
            print("Reusing existing " + name + ": " + path)
            self._done_set.add(path)
        return ret

    def _call_format(self, x, n):
        return cname(x) + "." + n + "()"

    def _call(self, origin, obj, fn, called):
        what = self._call_format(obj, fn)
        if what not in called:
            called.add(what)
            me = self._call_format(self, origin)
            print(me + " invoking " + what)
            getattr(obj, fn)(called)
            print("Resuming " + me)

    def _body(self, lvl, chk, called):
        """
        A helper function used to automate the logic of invoking dependencies and body
        Note: for lvl = license, license files are force cleaned!
        @param lvl: The clean level to be used for this
        @param chk: A dict where each entry contains the arguments to give to _done
        @param called: The set of already called methods
        If all calls to self._done pass, skip this stage
        If chk is empty, this stage will not be skipped
        """
        # Skip if everything is done
        if len(chk) and all([self._done(*i) for i in chk.items()]):
            return
        # Call dependent levels
        next = None
        lvl_name = lvl.name.lower()
        try:
            next = lvl.inc().name.lower()
        except ValueError:
            pass
        if next is not None:
            self._call(lvl_name, self, next, called)
        # Call current level dependencies
        for obj in self._dependencies:
            self._call(lvl_name, obj, lvl_name, called)
        getattr(self, "_" + lvl_name)()
        me = self._call_format(self, lvl_name)
        called.add(me)

    def get(self, called=None):
        """
        Acquire source files for this class and dependencies
        May reuse existing files
        """
        called = set() if called is None else called
        self._body(CleanLevel.GET, self._get_chk, called)

    def build(self, called=None):
        """
        Build libraries for this class and dependencies
        """
        called = set() if called is None else called
        self._body(CleanLevel.BUILD, self._build_chk, called)

    def license(self, called=None):
        """
        Install library licenses; will call ._license if it has not been called
        May reuse existing files
        """
        called = set() if called is None else called
        self._body(CleanLevel.LICENSE, {}, called)

    def install(self, called=None):
        """
        Install libraries and source files for this class and dependencies
        May reuse existing files
        """
        called = set() if called is None else called
        self._body(CleanLevel.INSTALL, self._install_chk, called)

    def clean(self, level: CleanLevel):
        """
        Cleans up after the library
        """
        p = lambda x: x.__class__.__name__ + ".clean(" + level.name + ")"
        for i in self._dependencies:
            print(p(self) + " invoking " + p(i))
            i.clean(level)
        self._clean(level)

    def _get(self):
        """
        A function subclasses should override to get source files
        No need to handle dependencies in this
        """
        pass

    def _build(self):
        """
        A function subclasses should override to build libraries
        No need to handle dependencies in this
        """
        pass

    def _license(self):
        """
        A function subclasses must override to install licenses
        No need to handle dependencies in this
        """
        raise RuntimeError("No licenses installed")

    def _install(self):
        """
        A function subclasses should override to install libaries
        No need to handle dependencies in this
        """
        pass

    def _clean(self, level):
        """
        A function subclasses should override to clean up
        No need to handle dependencies in this
        """
        pass


class GMP(Library):
    """
    A class to manage GMP
    """

    _url = "https://ftp.gnu.org/gnu/gmp/gmp-6.2.1.tar.xz"
    _root = os.path.join(native, "gmp")
    _source = os.path.join(_root, "src")
    _build_dir = os.path.join(_root, "build")
    include_dir = os.path.join(_root, "include")
    lib_dir = os.path.join(_build_dir, ".libs")
    # We are ok with either static or shared, but we prefer shared
    _lib_default = BuiltLib("libgmp", lib_dir, permit_static=True, permit_shared=True)
    _lic_d = os.path.join(BuiltLib.install_dir, "LICENSE.GMP")
    _lib = _lib_default

    def __init__(self):
        get_chk = {"GMP source": self._source}
        build_chk = {
            "GMP license": os.path.join(self._source, "COPYINGv3"),
            "GMP library": self._lib,
            "GMP include directory": self.include_dir,
        }
        install_chk = {"GMP lib": self._lib.find_installed}
        super().__init__(get_chk, build_chk, install_chk)

    def _get(self):
        os.makedirs(self._root, exist_ok=True)
        url = self._url
        sha = "fd4829912cddd12f84181c3451cc752be224643e87fac497b69edddadc49b4f2"
        d, gmp = download_checksum_extract(
            "GMP source", self._root, url, sha, ".tar.xz"
        )
        print("Moving GMP source to: " + self._source)
        assert len(gmp) == 1, "gmp's tarball is weird"
        os.rename(gmp[0], self._source)
        os.rmdir(d)

    def _set_lib_type(self, config_log):
        """
        Determine the built library type
        Run this during the build stage, after the build!
        """
        with open(config_log) as f:
            lines = f.readlines()
        sh_lib_str = "Shared libraries:"
        lines = [i for i in lines if sh_lib_str in i]
        assert len(lines) == 1, "./configure gave weird output"
        is_static = lines[0].replace(sh_lib_str, "").strip() == "no"
        print("GMP lib type: " + ("static" if is_static else "shared"))
        lib_type = StaticLib if is_static else SharedLib
        self._lib = lib_type(self._lib.name, self._lib.build_dir)

    def _run(self, name, *args, _count=0):
        """
        A wrapper for run
        _count should only be used by this function
        """
        whitelist = string.ascii_lowercase + string.digits + "_-"
        log_f = "".join([i for i in name.lower().replace(" ", "_") if i in whitelist])
        log_f = os.path.join(self._build_dir, "setup-py-" + log_f)
        log_f += ("" if _count == 0 else "_" + str(_count)) + ".log"
        if os.path.exists(log_f):
            return self._run(name, *args, _count=_count + 1)
        with open(log_f, "w") as f:
            print(name + "...")
            print("  - Output file: " + log_f)
            sys.stdout.write("  - ")
            run_cmd_no_fail(*args, stdout=f, stderr=f)
        return log_f

    def _build(self):
        print("Copying source to build dir: " + self._build_dir)
        shutil.copytree(self._source, self._build_dir)  # Do not pollute source
        with chdir(self._build_dir):
            # GMP warnings:
            # 1. GMP's online docs are incomplete
            # 2. GMP's detection of ld's shared lib support is broken on at least macOS
            # TODO: host=none is slow
            # TODO: enable-shared=mpz ?
            # If GMP's build system refuses to use a shared library, fallback to static
            config_args = [
                "--with-pic",
                "--disable-static",
                "--enable-shared",
                "--host=none",
            ]
            self._set_lib_type(self._run("Configuring", "./configure", *config_args))
            # Building + Checking
            nproc = max(cpu_count() - 1, 1)
            makej = (find_exe("make"), "-j" + str(nproc))  # GMP requires make
            _ = self._run("Building GMP", *makej)
            _ = self._run("Checking GMP build", *makej, "check")
            # Include dir
            os.mkdir(self.include_dir)
            shutil.copy2(os.path.join(self._build_dir, "gmp.h"), self.include_dir)

    def _license(self):
        if not os.path.exists(self._lic_d):
            os.mkdir(self._lic_d)

        def cpy(src, dst):
            src = os.path.join(self._build_dir, src)
            dst = os.path.join(self._lic_d, dst)
            print("Copying " + src + " --> " + dst)
            shutil.copy2(src, dst)

        cpy("COPYINGv3", "GNU-GPLv3")
        cpy("AUTHORS", "AUTHORS")
        cpy("COPYING.LESSERv3", "GNU-LGPLv3")
        print("Generating README...")
        msg = "The compiled GMP library is licensed under the GNU LGPLv3. The library was built from unmodified source code which can be found at: "
        with open(os.path.join(self._lic_d, "README"), "w") as f:
            f.write(msg + self._url)

    def _install(self):
        self._lib.install()

    def _clean(self, level):
        if level.implies(CleanLevel.INSTALL):
            self._lib.clean_install()
        if level.implies(CleanLevel.LICENSE):
            shutil.rmtree(self._lic_d, ignore_errors=True)
        if level.implies(CleanLevel.BUILD_DEPS):
            shutil.rmtree(self._build_dir, ignore_errors=True)
            shutil.rmtree(self.include_dir, ignore_errors=True)
            self._lib.clean_build()
            self._lib = self._lib_default  # Reset lib type
        if level.implies(CleanLevel.GET):
            shutil.rmtree(self._root, ignore_errors=True)


class Boost(Library):
    """
    A class used to manage Boost
    """

    root = os.path.join(native, "boost")
    _inc = os.path.join(root, "boost")
    _lic = os.path.join(root, "LICENSE")

    def __init__(self):
        chk = {"boost headers": self._inc, "boost license": self._lic}
        # Boost depends on GMP
        super().__init__(chk, {}, {}, GMP())

    @staticmethod
    def url_data():
        return {
            # Get this info from: https://www.boost.org/users/download/
            "posix": (
                "https://boostorg.jfrog.io/artifactory/main/release/1.78.0/source/boost_1_78_0.tar.gz",
                "94ced8b72956591c4775ae2207a9763d3600b30d9d7446562c552f0a14a63be7",
                ".tar.gz",
            ),
            "nt": (
                "https://boostorg.jfrog.io/artifactory/main/release/1.78.0/source/boost_1_78_0.zip",
                "f22143b5528e081123c3c5ed437e92f648fe69748e95fa6e2bd41484e2986cc3",
                ".zip",
            ),
        }[os.name]

    def _get(self):
        self._clean(CleanLevel.GET)  # Do not operate on a dirty boost dir
        os.mkdir(self.root)
        d, fs = download_checksum_extract("boost headers", self.root, *self.url_data())
        print("Installing boost license...")
        if len(fs) != 1:
            raise RuntimeError("Boost should decompress into a single directory.")
        shutil.copy2(os.path.join(fs[0], "LICENSE_1_0.txt"), self._lic)
        print("Installing boost headers...")
        os.rename(os.path.join(fs[0], "boost"), os.path.join(self.root, "boost"))
        print("Cleaning temporary files...")
        shutil.rmtree(d)

    def _license(self):
        pass  # Nothing to install

    def _clean(self, level):
        if level.implies(CleanLevel.GET):
            if os.path.exists(self.root):
                shutil.rmtree(self.root)


class Z3(Library):
    """
    A class used to manage the z3 dependency
    Z3 has no dependencies; it should be pre-installed
    """

    _root = os.path.dirname(z3.__file__)
    include_dir = os.path.join(_root, "include")
    lib = SharedLib("libz3", os.path.join(_root, "lib"))

    def __init__(self):
        super().__init__({}, {}, {"Z3 library": self.lib.find_installed})

    # _get is simply that _root has been resolved
    # Z3's pip has no license file so nothing for us to copy

    def _build(self):
        assert self.lib.find_built(), "Z3 is missing"

    def _license(self):
        pass  # Nothing to install


class Backward(Library):
    """
    A class used to manage the backward dependency
    """

    def __init__(self):
        # TODO: https://sourceware.org/elfutils/
        # TODO: https://sourceware.org/elfutils/ftp/0.186/
        # TODO: these depend on libdebuginfod (=dummy is an option?)
        super().__init__({}, {}, {})

    def _get(self):
        bk = os.path.join(native, "backward-cpp")
        b = os.path.exists(bk)
        assert b, "Backward is missing; run: git submodule init --recursive"
        lic = os.path.join(bk, "LICENSE.txt")
        assert os.path.exists(lic), "Backward missing license"

    def _license(self):
        pass  # Nothing to install


class Pybind11(Library):
    """
    A class used to manage the backward dependency
    """

    def __init__(self):
        super().__init__({}, {}, {})

    def _get(self):
        root = os.path.join(native, "pybind11")
        b = os.path.exists(root)
        assert b, "pybind11 is missing; run: git submodule init --recursive"
        lic = os.path.join(root, "LICENSE")
        assert os.path.exists(lic), "pybind11 missing license"

    def _license(self):
        pass  # Nothing to install


class Claricpp(Library):
    """
    A class to manage Claricpp
    """

    # Constants
    build_dir = os.path.join(native, "build")
    _lib = SharedLib("libclaricpp", build_dir)
    _out_native_src = os.path.join(BuiltLib.install_dir, "cpp_src")
    # API constants
    _api_target = "clari"
    _api_lib = SharedLib(_api_target, os.path.join(build_dir, "api"))
    # Docs constants
    _docs_dir = os.path.join(build_dir, "docs")  # Must be in build_dir

    def __init__(
        self, *, api, no_build=False, no_lib=False, docs=False, debug=False, tests=False
    ):
        # Options
        self._build_lib = not no_lib
        self._build_tests = tests
        self._build_debug = debug
        self._build_doc = docs
        self._build_api = api
        self._no_build = no_build
        # Config
        default_chk = {i.name: i for i in [self._lib, self._api_lib]}
        default_chk["C++ Source files"] = self._out_native_src
        chk = {} if (self._build_tests or self._build_doc) else default_chk
        super().__init__({}, chk, chk, Boost(), Z3(), Pybind11(), Backward())

    def _cmake_args(self):
        """
        Create arguments to pass to cmake for configuring claricpp
        """
        z3_built = Z3.lib.find_built()
        assert z3_built is not None, "z3 was not built"
        config = {
            "VERSION": version,
            "CLARICPP": claricpp,
            # Build options
            "BUILD_TESTS": self._build_tests,
            "BUILD_DOC": self._build_doc,
            "BUILD_API": self._build_api,
            # Debug options
            "CONSTANT_LOG_LEVEL": not self._build_debug,
            "DEFAULT_RELEASE_LOG_LEVEL": "critical",
            "CMAKE_BUILD_TYPE": "Debug" if self._build_debug else "Release",
            # Backtrace options
            "WARN_BACKWARD_LIMITATIONS": True,
            "REQUIRE_BACKWARD_BACKEND": False,
            # Disable options
            "CPP_CHECK": False,
            "CLANG_TIDY": False,
            "ENABLE_MEMCHECK": False,
            "LWYU": False,
            # Library config
            "GMPDIR": GMP.lib_dir,
            "GMP_INCLUDE_DIR": GMP.include_dir,
            "Boost_INCLUDE_DIRS": Boost.root,
            "Z3_ACQUISITION_MODE": "PATH",
            "Z3_INCLUDE_DIR": Z3.include_dir,
            "Z3_LIB": z3_built,
        }
        on_off = lambda x: ("ON" if x else "OFF") if type(x) is bool else x
        dd = lambda key, val: "-D" + key + "=" + ("" if val is None else on_off(val))
        return [dd(*i) for i in config.items()]

    def _build(self):
        if not os.path.exists(self.build_dir):
            os.mkdir(self.build_dir)
        # CMake
        print("Configuring...")
        with chdir(self.build_dir):
            run_cmd_no_fail(find_exe("cmake"), *self._cmake_args(), native)
        # Build
        if not self._no_build:
            targets = [  # Order matters (for cleaner output)
                (self._build_lib, claricpp),
                (self._build_tests, "unit_tests"),
                (self._build_doc, "docs"),
                (self._build_api, self._api_target),
            ]
            targets = [i[1] for i in targets if i[0]]
            with chdir(self.build_dir):
                for i in targets:
                    build_cmake_target(i)
                if self._build_doc:
                    print("Docs built in: " + self._docs_dir)

    @classmethod
    def run_tests(cls):  # Warning: tests should be built before calling this
        # Prefer ctest over make test but either will work
        with chdir(cls.build_dir):
            ctest = find_exe("ctest")
            if ctest is not None:
                run_cmd_no_fail(ctest, "-j" + str(max(cpu_count() - 1, 1)), ".")
            else:
                build_cmake_target("test")  # This will not be parallel

    def _license(self):
        pass  # Same as main project

    def _install(self):
        if self._build_lib:
            self._lib.install()
        if self._build_api:
            self._api_lib.install()
        if not os.path.exists(self._out_native_src):
            def ign(d, fs):
                rv = shutil.ignore_patterns("*.cpp", "*.hpp", "*.c", "*.h")(d, fs)
                return [ i for i in fs if i not in rv ]

            tmp = tempfile.mkdtemp(dir=self.build_dir, prefix="src-copy", suffix=".tmp")
            print("Generating output source in: " + tmp)
            for i in ["src", "api"]:
                src = os.path.join(native, i)
                dst = os.path.join(tmp, i)
                shutil.copytree(src, dst, ignore=ign)
            print("Installing output source...")
            os.rename(tmp, self._out_native_src)

    def _clean(self, level):
        if level.implies(CleanLevel.INSTALL):
            self._api_lib.clean_install()
            self._lib.clean_install()
            shutil.rmtree(self._out_native_src, ignore_errors=True)
        if level.implies(CleanLevel.BUILT_LIBS):
            self._api_lib.clean_build()
            self._lib.clean_build()
        if level.implies(CleanLevel.BUILD):
            if os.path.exists(self.build_dir):
                if os.path.exists(os.path.join(self.build_dir, "Makefile")):
                    with chdir(self.build_dir):
                        build_cmake_target("clean")
                shutil.rmtree(self.build_dir, ignore_errors=True)


######################################################################
#                             setuptools                             #
######################################################################


class SDist(SDistOriginal):
    def run(self):
        f = lambda: Claricpp(api=True).get()
        self.execute(f, (), msg="Getting build source dependencies")
        super().run()


class Native(Command):
    description = "Build native components"
    cmake_msg = "Do not build any Claricpp objects, stop after running cmake"
    docs_msg = "Build Claricpp docs; if --test builds test docs also; if not --no-api build API docs also"
    user_options = [
        ("no-install", None, "Do not install built libraries"),
        ("no-build", None, cmake_msg),
        ("no-lib", None, "Do not build the Claricpp library"),
        ("no-api", None, "Do not build the Claricpp API"),
        ("docs", None, docs_msg),
        ("override", None, "Ignore options sanity checks. Do not do this"),
        ("tests", "t", "Build Claricpp unit tests"),
        ("run-tests", None, "Run Claricpp tests"),
        ("debug", "d", "Prefers debug mode to release mode while building"),
        ("clean=", "c", "Runs clean at the given level first"),
    ]

    def initialize_options(self) -> None:
        self.args = [i for i in self.user_options if "=" not in i]  # Bools only
        self.args = [i[0].replace("-", "_") for i in self.args]
        _ = [setattr(self, i, None) for i in self.args]
        self.clean = None  # We will put this in args later

    def finalize_options(self) -> None:
        # Namespace args and make them bools here
        self.args = {i: (getattr(self, i) is not None) for i in self.args}
        # Add clean to args and freeze arg keys
        if self.clean is not None:
            self.clean = to_clean_lvl(self.clean)
        self.args["clean"] = self.clean
        self.args = JDict(self.args)
        # Error checking + cleanup
        _ = [delattr(self, i) for i in self.args]
        if self.args.no_lib and not self.args.no_build:
            print("Warning: --no-lib has no effect given --no-build")
        msgs = []
        if self.args.no_build and not self.args.no_install:
            msgs.append("--no-build will likely fail without --no-install")
        if self.args.run_test and self.args.no_build:
            msgs.append("--run-tests will likely fail without --no-build")
        if self.args.run_test and not self.args.tests:
            raise RuntimeError("--run-tests will likely fail without --tests")
        if self.args.no_lib and not self.args.no_api:
            msg = "--no-lib will likely fail without --no-api; unless --no-build is passed"
            msgs.append(msg)
        if self.args.no_lib and self.args.tests:
            msg = "--no-lib will likely fail with --tests; unless --no-build is passed"
            msgs.append(msg)
        if self.args.no_lib and self.args.run_tests:
            msgs.append("--no-lib will likely fail with --run_tests")
        # Allow sanity check override
        msg = "Options sanity check errors:\n  - " + "\n  - ".join(msgs)
        if len(msgs) > 0:
            if not self.args.override:
                raise RuntimeError(msg)
            print("Overriding o" + msg[1:])

    def run(self) -> None:
        # Construct the main class and determine the function name
        params = ["no_lib", "docs", "tests", "debug", "no_build"]
        params = {i: k for i, k in self.args.items() if i in params}
        instance = Claricpp(**params, api=not self.args.no_api)
        fname = "build" if self.args.no_install else "install"
        # Message
        msg = "Building native components"
        options = ["--" + i.replace("_", "-") for i, k in self.args.items() if k]
        if len(options) > 0:
            msg += " with options: " + " ".join(options)
        # Run
        if self.args.clean is not None:
            msg = "Cleaning Claricpp at level: " + self.args.clean.name
            self.execute(lambda: instance.clean(self.args.clean), (), msg=msg)
        self.execute(lambda: getattr(instance, fname)(), (), msg=msg)
        if self.args.run_tests:
            self.execute(instance.run_tests, (), msg="Running native tests")


class Build(BuildOriginal):
    def run(self):
        self.run_command("native")
        super().run()


class Clean(Command):
    user_options = [("level=", "l", "Clean")]

    def initialize_options(self) -> None:
        self.level = "GET"

    def finalize_options(self) -> None:
        self.level = to_clean_lvl(self.level)

    def run(self):
        f = lambda: Claricpp(api=True).clean(self.level)
        self.execute(f, (), msg="Cleaning Claricpp at level: " + self.level.name)


if __name__ == "__main__":
    setup(
        cmdclass={
            "sdist": SDist,
            "build": Build,
            # Custom commands
            "native": Native,
            "clean": Clean,
        },
    )
