from distutils.command.build import build as _build
from distutils.command.clean import clean as _clean
from distutils.command.sdist import sdist as _sdist
from native.build_ffi import build_ffi_wrapper
from setuptools import find_packages, setup
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
import shutil
import errno
import sys
import os
import re

# Shared libraries
import z3


# TODO: make install put stuff in claricpp build dir and such before building so that rpath is .


######################################################################
#                              Globals                               #
######################################################################


setup_file = os.path.abspath(__file__)
claripy = os.path.dirname(setup_file)
native = os.path.join(claripy, "native")

with open(os.path.join(claripy, "VERSION")) as f:
    version = f.read().strip()

# Claricpp library names; these should be in MANIFEST.in
claricpp = "claricpp"
claricpp_ffi = "claricpp_ffi"


######################################################################
#                              Helpers                               #
######################################################################


class JDict(dict):
    """
    A read-only dict that allows . semantics
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


def nprocd(delta=1):
    """
    Return: `nproc` - delta or 1, whichever is larger
    """
    assert delta >= 0, "delta may not be negative"
    return max(cpu_count() - delta, 1)


def find_exe(name):
    """
    Akin to bash's which function
    """
    exe = shutil.which(name, mode=os.X_OK)
    if exe is None:
        raise RuntimeError("Cannot find " + name)
    return exe


class BuiltLib:
    """
    A shared or static library
    """

    def __init__(self, name, build_dir, *, permit_shared, permit_static):
        self.name = name
        self.build_dir = build_dir
        self.install_dir = os.path.join(claripy, "claripy/claricpp")
        # Determine extensions
        self._permit_shared = permit_shared
        self._permit_static = permit_static

    def _find_ext(self, where, ext):
        files = glob(os.path.join(where, self.name) + "*.*")
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

    def install(self):
        """
        Copies the library from build dir to install dir
        """
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


def parse_info_file(info_file):
    """
    Parses the info file cmake outputs
    """
    with open(info_file) as f:
        data = f.readlines()
    data = [i.split("=", 1) for i in data if len(i.strip()) > 0]
    return JDict({i[0].strip(): i[1].strip() for i in data})


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


def generator(name):
    """
    Find a build generator (e.g. make)
    """
    print("Finding generator...")
    is_make = name.endswith("make")
    makej = [name]  # TODO: test on windows; angr uses nmake /f Makefile-win
    try:
        if makej[0].endswith("make"):
            makej.append("-j" + str(nprocd()))
    except NotImplementedError:
        pass
    return makej, is_make


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
                chunk_size = 2 ** 16
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
    """

    INSTALL = 1
    BUILD = 2
    GET = 3


# 'Member functions' of CleanLevel
setattr(type(CleanLevel.GET), "implies", lambda self, o: self.value >= o.value)
setattr(type(CleanLevel.GET), "inc", lambda self: CleanLevel(self.value + 1))


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
        """
        self._done_set = set()
        self._dependencies = dependencies
        assert self._dep_check(type(self)), "Cyclical dependency found on: " + str(
            type(self)
        )
        # Done check lists
        self._get_chk = get_chk
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

    def _body(self, force, lvl, chk):
        """
        A helper function used to automate the logic of invoking dependencies and body
        @param force: True if old files should be purged instead of possible reused
        @param lvl: The clean level to be used for this
        @param chk: A dict where each entry contains the arguments to give to _done
        If all calls to self._done pass, skip this stage
        If chk is empty, this stage will not be skipped
        """
        # Clean if needed
        if force:
            self.clean(lvl)
        # Skip if everything is done
        elif len(chk) and all([self._done(*i) for i in chk.items()]):
            return
        # Call dependent levels
        try:
            getattr(self, lvl.inc().name.lower())(force)
        except ValueError:
            pass
        # Call current level dependencies
        fn = lvl.name.lower()
        helper = lambda x, n: x.__class__.__name__ + "." + n + "()"
        for i in self._dependencies:
            print(helper(self, fn) + " invoking " + helper(i, fn))
            getattr(i, fn)(force)
        getattr(self, "_" + fn)()

    def get(self, force):
        """
        Acquire source files for this class and dependencies
        If force: ignores existing files, else may reuse existing files
        """
        self._body(force, CleanLevel.GET, self._get_chk)

    def build(self, force):
        """
        Build libraries for this class and dependencies
        If force: ignores existing files, else may reuse existing files
        """
        self._body(force, CleanLevel.BUILD, self._build_chk)

    def install(self, force):
        """
        Install libraries and source files for this class and dependencies
        If force: ignores existing files, else may reuse existing files
        """
        self._body(force, CleanLevel.INSTALL, self._install_chk)

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

    _root = os.path.join(native, "gmp")
    _source = os.path.join(_root, "src")
    _build_dir = os.path.join(_root, "build")
    include_dir = os.path.join(_root, "include")
    lib_dir = os.path.join(_build_dir, ".libs")
    # We are ok with either static or shared, but we prefer shared
    _lib_default = BuiltLib("libgmp", lib_dir, permit_static=True, permit_shared=True)
    _lib = _lib_default

    def __init__(self):
        get_chk = {"GMP source": self._source}
        build_chk = {
            "GMP library": self._lib,
            "GMP include directory": self.include_dir,
        }
        install_chk = {"GMP source": self._lib.find_installed}
        super().__init__(get_chk, build_chk, install_chk)

    def _get(self):
        os.makedirs(self._root)
        url = "https://ftp.gnu.org/gnu/gmp/gmp-6.2.1.tar.xz"
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

    def _run(self, name, *args):
        """
        A wrapper for run
        """
        log_n = "setup-py-" + re.sub(r"\W+", "", args[0]) + ".log"
        log_f = os.path.join(self._build_dir, log_n)
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
            makej = ["make", "-j" + str(nprocd())]
            _ = self._run("Building GMP", *makej)
            _ = self._run("Checking GMP build", *makej, "check")
            # Include dir
            os.mkdir(self.include_dir)
            shutil.copy2(os.path.join(self._build_dir, "gmp.h"), self.include_dir)

    def _install(self):
        self._lib.install()

    def _clean(self, level):
        if level.implies(CleanLevel.INSTALL):
            self._lib.clean_install()
        if level.implies(CleanLevel.BUILD):
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

    def __init__(self):
        # Boost depends on GMP
        super().__init__({"boost headers": self.root}, {}, {}, GMP())

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
        d, fs = download_checksum_extract("boost headers", native, *self.url_data())
        print("Installing boost headers...")
        if len(fs) != 1:
            raise RuntimeError("Boost should decompress into a single directory.")
        os.mkdir(self.root)
        os.rename(os.path.join(fs[0], "boost"), os.path.join(self.root, "boost"))
        print("Cleaning temporary files...")
        shutil.rmtree(d)

    def _clean(self, level):
        if level.implies(CleanLevel.GET):
            shutil.rmtree(self.root, ignore_errors=True)


class Z3(Library):
    """
    A class used to manage the z3 dependency
    Z3 has no dependencies; it should be pre-installed
    """

    _root = os.path.dirname(z3.__file__)
    include_dir = os.path.join(_root, "include")
    lib = SharedLib("libz3", os.path.join(_root, "lib"))

    def __init__(self):
        super().__init__({}, {}, {"Z3 library": self.lib.find_installed}, GMP())

    # _get is simply that _root has been resolved

    def _build(self):
        assert self.lib.find_built(), "Z3 is missing"

    def _install(self):
        self.lib.install()

    def _clean(self, level):
        if level.implies(CleanLevel.INSTALL):
            self.lib.clean_install()


class Backward(Library):
    """
    A class used to manage the backward dependency
    """

    def __init__(self):
        super().__init__({}, {}, {})

    def _get(self):
        b = os.path.exists(os.path.join(native, "backward"))
        assert b, "Backward is missing; run: git submodule init --recursive"


class Claricpp(Library):
    """
    A class to manage Claricpp
    """

    build_dir = os.path.join(native, "build")
    info_file = os.path.join(build_dir, "_for_setup_py.txt")
    _lib = SharedLib("libclaricpp", build_dir)

    def __init__(self):
        chk = {self._lib.name: self._lib}
        super().__init__({}, chk, chk, Boost(), Z3(), Backward())

    @staticmethod
    def _cmake_config_args(out_file, claricpp):
        """
        Create arguments to pass to cmake for configuring claricpp
        """
        z3_built = Z3.lib.find_built()
        assert z3_built is not None, "z3 was not built"
        config = {
            "VERSION": version,
            "CLARICPP": claricpp,
            "FOR_SETUP_PY_F": out_file,
            # Build options
            "CMAKE_BUILD_TYPE": "RelWithDebInfo",
            "WARN_BACKWARD_LIMITATIONS": True,
            "REQUIRE_BACKWARD_BACKEND": False,  # TODO: ask fish
            # Disable build options
            "ENABLE_TESTING": False,
            "CPP_CHECK": False,
            "CLANG_TIDY": False,
            "ENABLE_MEMCHECK": False,
            "BUILD_DOC": False,
            "LWYU": False,
            # Library config
            "GMPDIR": GMP.lib_dir,
            "GMP_INCLUDE_DIR": GMP.include_dir,
            "Boost_INCLUDE_DIRS": Boost.root,
            "Z3_INCLUDE_DIR": Z3.include_dir,
            "Z3_LIB": z3_built,
            "Z3_ACQUISITION_MODE": "PATH",
        }
        on_off = lambda x: ("ON" if x else "OFF") if type(x) is bool else x
        return ["-D" + i + "=" + on_off(k) for i, k in config.items()]

    @classmethod
    def _cmake(cls, native, build, info_file):
        print("Configuring...")
        cmake_args = cls._cmake_config_args(cls.info_file, claricpp)
        with chdir(build):
            run_cmd_no_fail(find_exe("cmake"), *cmake_args, native)
        return parse_info_file(info_file)

    def _build(self):
        os.mkdir(self.build_dir)
        cmake_out = self._cmake(native, self.build_dir, self.info_file)
        makej, is_make = generator(cmake_out.CMAKE_MAKE_PROGRAM)
        print("Building " + claricpp + "...")
        with chdir(self.build_dir):
            run_cmd_no_fail(*makej, claricpp)

    def _install(self):
        self._lib.install()

    def _clean(self, level):
        if level.implies(CleanLevel.INSTALL):
            self._lib.clean_install()
        if level.implies(CleanLevel.BUILD):
            shutil.rmtree(self.build_dir, ignore_errors=True)
            self._lib.clean_build()


class ClaricppFFI(Library):
    """
    A class to manage ClaricppFFI
    """

    _build_dir = os.path.join(Claricpp.build_dir, "ffi")
    _lib = SharedLib("claricpp", _build_dir)

    def __init__(self):
        chk = {self._lib.name: self._lib}
        super().__init__({}, chk, chk, Claricpp())

    @staticmethod
    def _verify_generator_supported(makej, is_make):
        if not is_make:  # Make works, not sure about other generators
            var = "FFI_FORCE_BUILD_dir "
            if var in os.eniron:
                print(var + " is set! Forcing build with non-make generator.")
            else:
                print("Current generator: ", makej[0])
                raise RuntimeError(
                    "Unknown if non-make generators support intermediate file targets. Set the "
                    + var
                    + " environment variable to forcibly continue",
                    file=sys.stderr,
                )

    def _build(self):
        info = parse_info_file(Claricpp.info_file)
        intermediate_f = info.CDEFS_SOURCE_F + ".i"
        include_dirs = info.Python_INCLUDE_DIRS
        makej, is_make = generator(info.CMAKE_MAKE_PROGRAM)
        py_version = str(sys.version_info.major) + "." + str(sys.version_info.minor)
        print("Building " + claricpp + "FFI API...")
        with chdir(Claricpp.build_dir):
            # We care about the intermediate file and its target
            cdefs_target = os.path.relpath(intermediate_f, Claricpp.build_dir)
            # Build the cdefs intermediate file
            self._verify_generator_supported(makej, is_make)
            run_cmd_no_fail(*makej, cdefs_target)
            # Run build_ffi
            build_ffi_wrapper(
                input_lib=claricpp,
                output_lib=claricpp_ffi,
                build_dir=Claricpp.build_dir,
                ffi_dir=self._build_dir,
                intermediate_f=intermediate_f,
                include_dirs="/include/python" + py_version + ";" + include_dirs,
                verbose=True,
            )

    def _install(self):
        self._lib.install()

    def _clean(self, level):
        if level.implies(CleanLevel.INSTALL):
            self._lib.clean_install()
        if level.implies(CleanLevel.BUILD):
            shutil.rmtree(self._build_dir, ignore_errors=True)
            self._lib.clean_build()


######################################################################
#                             setuptools                             #
######################################################################


class sdist(_sdist):
    def run(self, *args):
        f = lambda: ClaricppFFI().get(False)
        self.execute(f, (), msg="Getting build source dependencies")
        _sdist.run(self, *args)


class build(_build):
    def run(self, *args):
        f = lambda: ClaricppFFI().install(False)
        self.execute(f, (), msg="Getting build source dependencies")
        _build.run(self, *args)


class clean(_clean):
    def run(self, *args):
        lvl = os.getenv("SETUP_PY_CLEAN_LEVEL", "get").upper()
        print("Clean level set to: " + lvl)
        f = lambda: ClaricppFFI().clean(getattr(CleanLevel, lvl))
        self.execute(f, (), msg="Cleaning claripy/native")
        _clean.run(self, *args)


if __name__ == "__main__":
    setup(
        name="claripy",
        version=version,
        python_requires=">=3.6",
        packages=find_packages(),
        install_requires=[
            "z3-solver>=4.8.5.0",
            "future",
            "cachetools",
            "decorator",
            "pysmt>=0.9.1.dev119",
            "six",
        ],
        description="An abstraction layer for constraint solvers",
        url="https://github.com/angr/claripy",
        cmdclass={"sdist": sdist, "build": build, "clean": clean},
        include_package_data=True,
        package_data={"claripy": ["claricpp/*"]},
    )
