from distutils.command.build import build as _build
from distutils.command.clean import clean as _clean
from distutils.command.sdist import sdist as _sdist
from setuptools import find_packages, setup
from multiprocessing import cpu_count
from contextlib import contextmanager
from hashlib import sha256
from enum import Enum
from glob import glob
import subprocess
import requests
import tempfile
import shutil
import sys
import os
import re

# Shared libraries
import z3


if bytes is str:
    raise Exception(
        "This module is designed for python 3 only. Please install an older version to use python 2."
    )


######################################################################
#                              Globals                               #
######################################################################


setup_file = os.path.abspath(__file__)
claripy = os.path.dirname(setup_file)
native = os.path.join(claripy, "native")

with open(os.path.join(claripy, "VERSION")) as f:
    version = f.read().strip()

# Claricpp library names
# If these are changed, MANIFEST.in needs to be updated as well
claricpp = "claricpp"
claricpp_ffi = "claricpp_ffi"

# Python version
py_version = str(sys.version_info.major) + "." + str(sys.version_info.minor)


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

    def __init__(
        self, name: str, build_dir: str, *, permit_shared: bool, permit_static: bool
    ):
        self.name = name
        self.build_dir = build_dir
        self._install_dir = os.path.join(claripy, "claripy/claricpp")
        # Determine extensions
        self._extensions = []
        self._extensions.extend([".so", ".dylib", ".dll"] if permit_shared else [])
        self._extensions.extend([".a"] if permit_static else [])

    def _find(self, where):
        """
        Tries to find a library within the directory where
        """
        is_lib = lambda x: any(x.endswith(i) for i in self._extensions)
        files = glob(os.path.join(where, self.name) + "*.*")
        files = [i for i in files if is_lib(i)]
        if len(files) == 1:
            return files[0]
        if len(files) > 1:
            print("Found: " + str(files))
            raise RuntimeError("Multiple " + self.name + " libraries in ", where)

    def find_installed(self):
        """
        Look for the library in the installation directory
        """
        return self._find(self._install_dir)

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
        shutil.copy2(p, self._install_dir)

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
    print("Downloading " + name + "...")
    hasher = sha256()
    prefix = re.sub(r"\s+", "_", name) + "-"
    fd, comp_f = tempfile.mkstemp(dir=where, prefix=prefix, suffix=ext)
    with os.fdopen(fd, "wb") as f:
        with requests.get(url, allow_redirects=True, stream=True) as r:
            r.raise_for_status()
            for block in r.iter_content(chunk_size=2 ** 16):
                hasher.update(block)
                f.write(block)
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
    """

    INSTALL = 1
    BUILD = 2
    GET = 3


# Safer version of >= for this enum
setattr(type(CleanLevel.GET), "implies", lambda self, o: self.value >= o.value)


######################################################################
#                         Dependency Classes                         #
######################################################################


class Library:
    """
    Native dependencies should derive from this
    """

    def __init__(self, *dependencies):
        self._dependencies = dependencies
        self._done_set = set()

    def _done(self, name, path):
        """
        If path exists, note it will be reused and return True
        This will only warn once per path!
        path may be None
        """
        ret = False if path is None else os.path.exists(path)
        if path in self._done_set:
            assert ret, path + " used to exist but now does not"
        elif ret:
            print("Reusing existing " + name + ": " + path)
            self._done_set.add(path)
        return ret

    def _log(self, name, val, o):
        fn = lambda x: x.__class__.__name__ + "." + name + "(" + str(val) + ")"
        print(fn(self) + " invoking dependency " + fn(o))

    def get(self, force):
        """
        Acquire source files for this class
        If force: ignores existing files, else reuses existing files
        Calls get(force) for each dependency
        """
        for i in self._dependencies:
            self._log("get", force, i)
            i.get(force)

    def build(self, force):
        """
        Builds dependency
        If force: ignores existing files, else reuses existing files
        Calls build(force) for each dependency
        Will call get(force) as needed
        """
        for i in self._dependencies:
            self._log("build", force, i)
            i.build(force)

    def install(self, force):
        """
        Installs dependency
        If force: ignores existing files, else reuses existing files
        Calls install(force) for each dependency
        Will call build(force) as needed
        """
        for i in self._dependencies:
            self._log("install", force, i)
            i.install(force)

    def clean(self, level: CleanLevel, recursive):
        """
        Cleans up after the library
        level can be 'get', 'build', or 'install'
        'get' implies 'build' which implies 'install'
        """
        for i in self._dependencies:
            self._log("clean", recursive, i)
            i.clean(level, recursive)


class GMP(Library):
    """
    A class to manage GMP
    """

    _root = os.path.join(native, "gmp")
    _source = os.path.join(_root, "src")
    _build = os.path.join(_root, "build")
    lib_dir = os.path.join(_build, ".libs")
    # We are ok with either static or shared, but we prefer shared
    _lib_default = BuiltLib("libgmp", lib_dir, permit_static=True, permit_shared=True)
    _lib = _lib_default

    def get(self, force):
        if force:
            shutil.rmtree(self._source, ignore_errors=True)
        super().get(force)
        if self._done("GMP source", self._source):
            return
        os.makedirs(self._root)
        url = "https://ftp.gnu.org/gnu/gmp/gmp-6.2.1.tar.xz"
        sha = "fd4829912cddd12f84181c3451cc752be224643e87fac497b69edddadc49b4f2"
        raw, gmp = download_checksum_extract(
            "GMP source", self._root, url, sha, ".tar.xz"
        )
        print("Installing GMP source")
        assert len(gmp) == 1, "gmp's tarball is weird"
        os.rename(gmp[0], self._source)
        os.rmdir(raw)

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

    def build(self, force):
        if force:
            shutil.rmtree(self._build, ignore_errors=True)
        super().build(force)  # Do this before done in case dep's were cleaned
        if self._done("GMP build directory", self._build):
            return
        self.get(force)
        print("Copying source to build dir: " + self._build)
        shutil.copytree(self._source, self._build)  # Do not pollute source
        with chdir(self._build):

            def run(name, *args):
                log_n = "setup-py-" + re.sub(r"\W+", "", args[0]) + ".log"
                log_f = os.path.join(self._build, log_n)
                with open(log_f, "w") as f:
                    print(name + " log file: " + log_f)
                    run_cmd_no_fail(*args, stdout=f, stderr=f)
                return log_f

            # GMP warnings:
            # 1. GMP's online docs are incomplete
            # 2. GMP's detection of ld's shared lib support is broken on at least macOS
            # TODO: host=none is slow
            # TODO: enable-shared=mpz ?
            # If GMP's build system refuses to use a shared library, fallback to static
            config_args = ["--disable-static", "--enable-shared", "--host=none"]
            self._set_lib_type(run("Configuring", "./configure", *config_args))
            # Building + Checking
            makej = ["make", "-j" + str(nprocd())]
            _ = run("Building GMP", *makej)
            _ = run("Checking GMP build", *makej, "check")

    def install(self, force):
        inst = self._lib.find_installed()
        if force and inst is not None:
            os.remove(inst)
        super().install(force)  # Do this before done in case dep's were cleaned
        if self._done("GMP", inst):
            return
        self.build(force)
        self._lib.install()

    def clean(self, level, recursive):
        if recursive:
            super().clean(level, recursive)
        if level.implies(CleanLevel.INSTALL):
            self._lib.clean_install()
        if level.implies(CleanLevel.BUILD):
            shutil.rmtree(self._build, ignore_errors=True)
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
        super().__init__(GMP())  # We depend on GMP

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

    def get(self, force):
        if force:
            shutil.rmtree(self.root, ignore_errors=True)
        super().get(force)
        if self._done("boost headers", self.root):
            return
        raw, uncomp = download_checksum_extract(
            "boost headers", native, *self.url_data()
        )
        print("Installing boost headers...")
        if len(uncomp) != 1:
            raise RuntimeError("Boost should decompress into a single directory.")
        os.rename(os.path.join(uncomp[0], "boost"), self.root)
        # Cleanup
        print("Cleaning temporary files...")
        shutil.rmtree(raw)

    def clean(self, level, recursive):
        if recursive:
            super().clean(level, recursive)
        if level.implies(CleanLevel.GET):
            shutil.rmtree(self.root, ignore_errors=True)


class Z3(Library):
    """
    A class used to install z3
    Z3 has no dependencies; it should be pre-installed
    """
    _root = os.path.dirname(z3.__file__)
    include_dir = os.path.join(_root, "include")
    _lib = SharedLib("libz3", os.path.join(_root, 'lib'))

    def build(self, force):
        inst = self._lib.find_installed()
        if force:
            os.remove(inst)


    def install(self, force):
        inst = self._lib.find_installed()
        if force:
            os.remove(inst)
        self.build(force)
        print(self._lib._install_dir)
        self._lib.install()

    def clean(self, level, _):
        if level.implies(CleanLevel.INSTALL):
            self._lib.clean_install()
        if level.implies(CleanLevel.BUILD):
            self._lib.clean_build()


class Claricpp(Library):
    """
    A class to manage Claricpp
    """

    build_dir = os.path.join(native, "build")
    info_file = os.path.join(build_dir, "_for_setup_py.txt")
    _lib = SharedLib("libclaricpp", build_dir)

    def __init__(self):
        super().__init__(Boost(), Z3())

    @staticmethod
    def _cmake_config_args(out_file, claricpp):
        """
        Create arguments to pass to cmake for configuring claricpp
        """
        config = {
            "FOR_SETUP_PY_F": out_file,
            "VERSION": version,
            "CLARICPP": claricpp,
            # Build options
            "CMAKE_BUILD_TYPE": "RelWithDebInfo",
            "ENABLE_TESTING": False,
            "CPP_CHECK": False,
            "CLANG_TIDY": False,
            "ENABLE_MEMCHECK": False,
            "LWYU": False,
            "WARN_BACKWARD_LIMITATIONS": True,
            # Library config
            "GMPDIR": GMP.lib_dir,
            "Boost_INCLUDE_DIRS": Boost.root,
            "Z3_INCLUDE_DIR": Z3.include_dir,
            "Z3_ACQUISITION_MODE": "PATH",
            "Z3_FORCE_CLEAN": "ON",
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

    def build(self, force):
        if force:
            shutil.rmtree(self.build_dir, ignore_errors=True)
        super().build(force)
        if self._done(self._lib.name, self._lib.find_built()):
            return
        self.get(force)  # Headers
        # Init
        if not os.path.exists(self.build_dir):
            os.mkdir(self.build_dir)
        # Build
        cmake_out = self._cmake(native, self.build_dir, self.info_file)
        makej, is_make = generator(cmake_out.CMAKE_MAKE_PROGRAM)
        print("Building " + claricpp + "...")
        with chdir(self.build_dir):
            run_cmd_no_fail(*makej, claricpp)

    def install(self, force):
        inst = self._lib.find_installed()
        if inst is not None and force:
            os.remove(inst)
        super().install(force)
        if self._done(self._lib.name, self._lib.find_installed()):
            return
        self.build(force)
        self._lib.install()

    def clean(self, level, recursive):
        if recursive:
            super().clean(level, recursive)
        if level.implies(CleanLevel.INSTALL):
            self._lib.clean_install()
        if level.implies(CleanLevel.BUILD):
            shutil.rmtree(self.build_dir, ignore_errors=True)
            self._lib.clean_build()


class ClaricppFFI(Library):
    """
    A class to manage ClaricppFFI
    """

    _build = os.path.join(Claricpp.build_dir, "ffi")
    _lib = SharedLib("claricpp", _build)

    def __init__(self):
        super().__init__(Claricpp())

    @staticmethod
    def _verify_generator_supported(makej, is_make):
        if not is_make:  # Make works, not sure about other generators
            var = "FFI_FORCE_BUILD "
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

    def build(self, force):
        if force:
            shutil.rmtree(self._build, ignore_errors=True)
        super().build(force)
        if self._done(self._lib.name, self._lib.find_built()):
            return
        # Get data from cmake
        info = parse_info_file(Claricpp.info_file)
        intermediate_f = info.CDEFS_SOURCE_F + ".i"
        include_dirs = info.Python_INCLUDE_DIRS
        makej, is_make = generator(info.CMAKE_MAKE_PROGRAM)
        print("Building " + claricpp + "FFI API...")
        with chdir(Claricpp.build_dir):
            # We care about the intermediate file and its target
            cdefs_target = os.path.relpath(intermediate_f, Claricpp.build_dir)
            # Build the cdefs intermediate file
            self._verify_generator_supported(makej, is_make)
            run_cmd_no_fail(*makej, cdefs_target)
            # Run build_ffi
            sys.path.append(native)
            from build_ffi import build_ffi_wrapper

            sys.path.pop()
            build_ffi_wrapper(
                input_lib=claricpp,
                output_lib=claricpp_ffi,
                build_dir=Claricpp.build_dir,
                ffi_dir=self._build,
                intermediate_f=intermediate_f,
                include_dirs="/include/python" + py_version + ";" + include_dirs,
                verbose=True,
            )

    def install(self, force):
        inst = self._lib.find_installed()
        if inst is not None and force:
            os.remove(inst)
        super().install(force)
        if self._done(self._lib.name, self._lib.find_installed()):
            return
        self.build(force)
        self._lib.install()

    def clean(self, level, recursive):
        if recursive:
            super().clean(level, recursive)
        if level.implies(CleanLevel.INSTALL):
            self._lib.clean_install()
        if level.implies(CleanLevel.BUILD):
            shutil.rmtree(self._build, ignore_errors=True)
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
        f = lambda: ClaricppFFI().clean(getattr(CleanLevel, lvl), True)
        self.execute(f, (), msg="Cleaning claripy/native")
        _clean.run(self, *args)


if __name__ == '__main__':
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
