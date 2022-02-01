from distutils.command.build import build as _build
from distutils.command.clean import clean as _clean
from distutils.command.sdist import sdist as _sdist
from multiprocessing import cpu_count
import contextlib
import subprocess
import requests
import tempfile
import hashlib
import shutil
import glob
import sys
import os

# Python

from setuptools import setup
from setuptools import find_packages

if bytes is str:
    raise Exception(
        "This module is designed for python 3 only. Please install an older version to use python 2."
    )

with open(os.path.join(os.path.dirname(__file__), "VERSION")) as f:
    version = f.read().strip()

# Native

# Claricpp library names
# If these are changed, MANIFEST.in needs to be updated as well
claricpp = "claricpp"
claricpp_ffi = "claricpp_ffi"


######################################################################
#                       Global Path Management                       #
######################################################################

class JDict(dict):
    __getattr__ = dict.get
    __setattr__ = None
    __delattr__ = None

def dir_names(root):
    """
    Returns a dict of paths / dict of paths
    This is used for consistency
    ffi will be within build
    lib contains other files and already exists
    """
    import z3

    native_dir = os.path.join(root, "native")
    ret = JDict({
        "native": native_dir,
        "lib": os.path.join(root, "claripy/claricpp"),
        "z3": os.path.join(os.path.dirname(z3.__file__), "include"),
    })
    assert os.path.isdir(ret["lib"]), "Claripy directory is missing " + ret["lib"]
    return ret

# We make this global since everything will use it
ds = dir_names(os.path.dirname(__file__))

######################################################################
#                              Helpers                               #
######################################################################


@contextlib.contextmanager
def chdir(new):
    """
    Current working directory context manager
    """
    old = os.getcwd()
    try:
        os.chdir(new)
        yield
    finally:
        os.chdir(old)

def nprocd(delta = 1):
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


class SLib():
    def __init__(self, name, build_dir, install_dir):
        self._name = name
        self._build_dir = build_dir
        self._install_dir = install_dir
    def _find(self, where, allow_missing):
        """
        Tries to find a library within the directory where
        """
        is_lib = lambda x: x.endswith(".so") or x.endswith(".dylib") or x.endswith(".dll")
        files = glob.iglob(os.path.join(where, self._name + "*.*"))
        files = [i for i in files if is_lib(i)]
        if len(files) > 1:
            print("Found: " + str(files))
            raise RuntimeError("Could not find definitive lib: " + self._name + " in ", where)
        if len(files) == 0:
            if allow_missing:
                return None
            raise RuntimeError("Could not find lib: " + self._name + " in ", where)
        return files[0]
    def find_installed(self, allow_missing):
        """
        Look for the library in the installation directory
        """
        return self._find(self._install_dir, self._name, allow_missing)
    def find_built(self, *, allow_missing):
        """
        Look for the library in the build directory
        """
        return self._find(self._build_dir, self._name, allow_missing)
    def install(self):
        """
        Copies the library from build dir to install dir
        """
        p = self.find_built()
        assert p is not None, "Cannot install a non-built library"
        shutil.copy2(p, self._install_dir)
    def clean(self):
        """
        Removes name from chdir and installed directories
        """
        where = [self.find_built(), self.find_installed()]
        _ = [ os.remove(i) for i in where is i is not None ]


def cmake_config_args(out_file, claricpp):
    """
    Create arguments to pass to cmake for configuring claricpp
    """
    # Config
    raw_config = {
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
        "Boost_INCLUDE_DIRS": Boost.root,
        "Z3_INCLUDE_PATH": ds.z3,
        "Z3_ACQUISITION_MODE": "SYSTEM",
        "Z3_FORCE_CLEAN": "ON",
    }
    # Overrides
    def override(what):
        val = os.environ.get(what, None)
        if val is not None:
            raw_config[what] = val

    override("Z3_INCLUDE_PATH")
    override("DEFAULT_RELEASE_LOG_LEVEL")
    # Gen config
    def format(key, value):
        value = value if type(value) is not bool else ("ON" if value else "OFF")
        return "-D" + str(key) + "=" + str(value)

    return [format(i, k) for i, k in raw_config.items()]


def parse_info_file(info_file):
    """
    Parses the info file cmake outputs
    """
    with open(info_file) as f:
        data = f.readlines()
    data = [i.split("=", 1) for i in data if len(i.strip()) > 0]
    return JDict({i[0].strip(): i[1].strip() for i in data})


def run_cmd_no_fail(*args):
    """
    A wrapper around subprocess.run that errors on subprocess failure
    """
    args = list(args)
    print("Running: subprocess.run(" + str(args) + ")")
    rc = subprocess.run(args)
    if rc.returncode != 0:
        what = os.path.basename(args[0])
        raise RuntimeError(what + " failed with return code: " + str(rc.returncode))
    return rc


def extract(d, f, ext):
    """
    Extract f into d given, the compression is assumed from the extension (ext)
    No leading period is allowed in ext
    """
    if ext == "tar.gz":
        import tarfile

        with tarfile.open(f) as z:
            z.extractall(d)
    elif ext == "zip":
        from zipfile import ZipFile

        with ZipFile(f) as z:
            z.extractall(d)
    else:
        raise RuntimeError("Compression type not supported")

    py_version = str(sys.version_info.major) + "." + str(sys.version_info.minor)

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


######################################################################
#                         Dependency Classes                         #
######################################################################


class Library:
    """
    Native dependencies should derive from this
    """
    def __init__(self, *dependencies):
        self._deps = dependencies
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

    def get(self, force):
        """
        Acquire source files for this class
        If force: ignores existing files, else reuses existing files
        Calls get(force) for each dependency
        """
        _ = [ i.get(force) for i in self._dependencies ]

    def build(self, force):
        """
        Builds dependency
        If force: ignores existing files, else reuses existing files
        Calls build(force) for each dependency
        """
        _ = [ i.build(force) for i in self._dependencies ]

    def install(self, force):
        """
        Installs dependency
        If force: ignores existing files, else reuses existing files
        Calls install(force) for each dependency
        """
        _ = [ i.install(force) for i in self._dependencies ]

    def clean(self, recursive):
        """
        Cleans up after the library
        """
        if recursive:
            _ = [ i.clean() for i in self._dependencies ]


class GMP(Library):
    """
    A class to manage GMP
    """
    _root = os.path.join(ds.native, "gmp")
    _src = os.path.join(_root, "src")
    _build = os.path.join(_root, "build")
    _lib = SLib("libgmp", ds.gmp.build, ds.install)

    def get(self, *, force = False):
        if force:
            shutil.rmtree(self._source, ignore_errors=True)
        super().get(force)
        if self._done("GMP source", self._source):
            return
        os.makedirs(self._source)
        print("Downloading GMP source to: ", self._source)
        run_cmd_no_fail("hg", "clone", "https://gmplib.org/repo/gmp/", self._source)

    def build(self, force = False):
        if force_new:
            shutil.rmtree(self._build, ignore_errors=True)
        super().build(force) # Do this before done in case dep's were cleaned
        if self._done("GMP build directory", self._build):
            return
        self.get(force)
        os.mkdir(self._build)
        # Bootstrap
        with chdir(self._source):
            print("Bootstrap...")
            run_cmd_no_fail(os.path.join(self._source, ".bootstrap"))
            # Configure
            os.chdir(self._build)
            print("Configuring in: " + self._build)
            config_args = ["--disable-static", "--host=none"] # TODO: host=none is slow
            run_cmd_no_fail(os.path.join(self._source, "configure"), config_args)
            # Building
            print("Building GMP...")
            makej = [ "make", "-j" + str(nprocd()) ]
            run_cmd_no_fail(*makej)
            # Checking
            print("Checking GMP build...")
            run_cmd_no_fail(*makej, "check")

    def install(self, force = False):
        inst = self._lib.find_installed()
        if force_new and inst is not None:
            os.remove(inst)
        super().install(force) # Do this before done in case dep's were cleaned
        if self._done("GMP", inst):
            return
        self.build(force)
        # Installing
        import IPython
        IPython.embed() # TODO
        self._lib.install()

    def clean(self, recursive):
        if recursive:
            super().clean(recursive)
        shutil.rmtree(self._root, ignore_errors=True)
        self._lib.clean()

class Boost(Library):
    '''
    A class used to manage Boost
    '''
    root = os.path.join(ds.native, "boost")

    def __init__(self):
        super().__init__(GMP) # We depend on GMP

    @staticmethod
    def url_data():
        return {
            # Get this info from: https://www.boost.org/users/download/
            "posix": (
                "https://boostorg.jfrog.io/artifactory/main/release/1.78.0/source/boost_1_78_0.tar.gz",
                "94ced8b72956591c4775ae2207a9763d3600b30d9d7446562c552f0a14a63be7",
                "tar.gz",
            ),
            "nt": (
                "https://boostorg.jfrog.io/artifactory/main/release/1.78.0/source/boost_1_78_0.zip",
                "f22143b5528e081123c3c5ed437e92f648fe69748e95fa6e2bd41484e2986cc3",
                "zip",
            ),
        }[os.name]

    def get(self, *, force = False):
        if force:
            shutil.rmtree(self.root, ignore_errors=True)
        super().get(force)
        if self._done('boost headers', self.root):
            return
        # Config
        url, sha, ext = self.url_data()
        # Get + checksum
        print("Downloading boost headers...")
        hasher = hashlib.sha256()
        fd, comp_f = tempfile.mkstemp(prefix=ds.native, suffix="-boost." + ext)
        with os.fdopen(fd, "wb") as f:
            with requests.get(url, allow_redirects=True, stream=True) as r:
                r.raise_for_status()
                for block in r.iter_content(chunk_size=2 ** 16):
                    hasher.update(block)
                    f.write(block)
        if hasher.hexdigest() != sha:
            raise RuntimeError("Downloaded boost headers hash failure!")
        # Extract
        raw_boost = tempfile.mkdtemp(prefix=ds.native, suffix="-boost.tmp")
        print("Extracting boost headers to: " + raw_boost)
        extract(raw_boost, comp_f, ext)
        os.remove(comp_f)
        # Move into place
        print("Installing boost headers...")
        uncomp = glob.glob(os.path.join(raw_boost, "*"))
        if len(uncomp) != 1:
            raise RuntimeError("Boost should decompress into a single directory.")
        os.rename(os.path.join(uncomp[0], "boost"), self.root)
        # Cleanup
        print("Cleaning temporary files...")
        shutil.rmtree(raw_boost)

    def clean(self, recursive):
        if recursive:
            super().clean(recursive)
        shutil.rmtree(self.root, ignore_errors=True)

class Clarpcpp(Library):
    '''
    A class to manage Claricpp
    '''
    build_dir = os.path.join(ds.native, "build")
    info_file = os.path.join(build_dir, "_for_setup_py.txt")
    _lib = SLib("libclaricpp", build_dir, ds.install)

    def __init__(self):
        super().__init__(Boost) # We depend on Boost

    @staticmethod
    def _cmake(native, build, info_file):
        print("Configuring...")
        with chdir(build):
            info_file = os.path.join(build_dir, info_file)
            cmake_args = cmake_config_args(info_file, claricpp)
            run_cmd_no_fail(find_exe("cmake"), *cmake_args, native)
            return parse_info_file(info_file)

    def build(self, force):
        if force:
            shutil.rmtree(self.build_dir, ignore_errors=True)
        super().build(force)
        if self._done(self._lib.name, self._lib.find_built(True)):
            return
        self.get() # Headers
        # Init
        if not os.path.exists(self.build_dir):
            os.mkdir(self.build_dir)
        # Build
        cmake_out = self._make(self._native, self.build_dir, "_for_setup_py.txt")
        makej, is_make = generator(cmake_out.CMAKE_MAKE_PROGRAM)
        print("Building " + claricpp + "...")
        with chdir(self.build_dir):
            run_cmd_no_fail(*makej, claricpp)

    def install(self, force):
        inst = self._lib.find_installed()
        if inst is not None and force:
            os.remove(inst)
        super().install(force)
        if self._done(self._lib.name, self._lib.find_installed(True)):
            return
        self.build()
        self._lib.install()

    def clean(self, recursive):
        if recursive:
            super().clean(recursive)
        shutil.rmtree(self.build_dir, ignore_errors=True)
        self._lib.clean()

class ClaricppFFI(Library):
    """
    A class to manage ClaricppFFI
    """
    _build = os.path.join(Claricpp.build_dir, "ffi"),
    _lib = SLib("claricpp", _build, ds.install)

    def __init__(self):
        super().__init__(Claricpp)

    @staticmethod
    def _verify_generator_supported(makej, is_make):
        if not is_make: # Make works, not sure about other generators
            var = "FFI_FORCE_BUILD "
            if var not in os.eniron:
                print("Current generator: ", makej[0])
                raise RuntimeError("Unknown if non-make generators support intermediate file targets. Please set the " + var + " environment variable to forcibly continue", file=sys.stderr)
            else:
                print(var + " is set; forcing build with non-make generator; note that it is unknown if this generator supports intermediate file targets")

    def build(self, force):
        if force:
            shutil.rmtree(self._build, ignore_errors=True)
        super().build(force)
        if self._done(self._lib.name, self._lib.find_built(True)):
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
            sys.path.append(ds.native)
            from build_ffi import build_ffi_wrapper

            sys.path.pop()
            build_ffi_wrapper(
                input_lib=claricpp,
                output_lib=claricpp_ffi,
                build_dir=ds.build,
                ffi_dir=ds.ffi,
                intermediate_f=intermediate_f,
                include_dirs="/include/python" + py_version + ";" + include_dirs,
                verbose=True,
            )

    def install(self, force):
        inst = self._lib.find_installed()
        if inst is not None and force:
            os.remove(inst)
        super().install(force)
        if self._done(self._lib.name, self._lib.find_installed(True)):
            return
        self.build()
        self._lib.install()

    def clean(self, recursive):
        if recursive:
            super().clean(recursive)
        shutil.rmtree(self.build_dir, ignore_errors=True)
        self._lib.clean()


######################################################################
#                             setuptools                             #
######################################################################


class sdist(_sdist):
    def run(self, *args):
        self.execute(lambda: ClaricppFFI().get(), (), msg="Getting build source dependencies")
        _sdist.run(self, *args)


class build(_build):
    def run(self, *args):
        self.execute(lambda: ClaricppFFI().install(), (), msg="Getting build source dependencies")
        _build.run(self, *args)


class clean(_clean):
    def run(self, *args):
        self.execute(lambda: ClaricppFFI().clean(), (), msg="Cleaning claripy/native")
        _clean.run(self, *args)


cmdclass = {"sdist": sdist, "build": build, "clean": clean}

# Both

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
    cmdclass=cmdclass,
    include_package_data=True,
    package_data={"claripy": ["claricpp/*"]},
)
