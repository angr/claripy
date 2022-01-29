from distutils.command.build import build as _build
from distutils.command.clean import clean as _clean
from distutils.command.sdist import sdist as _sdist
from multiprocessing import cpu_count
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
#                              Helpers                               #
######################################################################


def dir_names(root):
    """
    Returns a dict of paths
    This is used for consistency
    ffi will be within build
    lib contains other files and already exists
    boost will be the child of native
    """
    import z3

    native_dir = os.path.join(root, "native")
    build_dir = os.path.join(native_dir, "build")
    ret = {
        "native": native_dir,
        "build": build_dir,
        "ffi": os.path.join(build_dir, "ffi"),
        "boost": os.path.join(native_dir, "boost"),
        "lib": os.path.join(root, "claripy/claricpp"),
        "z3" : os.path.join(os.path.dirname(z3.__file__), "include")
    }
    assert os.path.isdir(ret["lib"]), "Claripy directory is missing " + ret["lib"]
    return ret
d = dir_names(os.path.dirname(__file__))


def find_exe(name):
    """
    Akin to bash's which function
    """
    exe = shutil.which(name, mode=os.X_OK)
    if exe is None:
        raise RuntimeError("Cannot find " + name)
    return exe

def find_lib(base, name, *, allow_missing=True):
    """
    Tries to find a library named name within the directory base
    """
    is_lib = lambda x: x.endswith(".so") or x.endswith(".dylib") or x.endswith(".dll")
    files = glob.iglob(os.path.join(base, name + "*.*"))
    files = [ i for i in files if is_lib(i) ]
    if len(files) > 1:
        print("Found: " + str(files))
        raise RuntimeError("Could not find definitive lib: " + name + " in ", base)
    if len(files) == 0:
        if allow_missing:
            return None
        raise RuntimeError("Could not find lib: " + name + " in ", base)
    return files[0]


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
        "Boost_INCLUDE_DIRS" : d['boost'],
        "Z3_INCLUDE_PATH": d['z3'],
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
    return {i[0].strip(): i[1].strip() for i in data}


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
    if ext == 'tar.gz':
        import tarfile
        with tarfile.open(f) as z:
            z.extractall(d)
    elif ext == 'zip':
        from zipfile import ZipFile
        with ZipFile(f) as z:
            z.extractall(d)
    else:
        raise RuntimeError('Compression type not supported')


######################################################################
#                           Main Functions                           #
######################################################################


def get_boost():
    '''
    Download the boost headers and put them in d['boost']
    This *will* overwrite the existing d['boost'] directory
    '''
    # Config
    url, sha, ext = {
        # Get this info from: https://www.boost.org/users/download/
        "posix": (
            "https://boostorg.jfrog.io/artifactory/main/release/1.78.0/source/boost_1_78_0.tar.gz",
            "94ced8b72956591c4775ae2207a9763d3600b30d9d7446562c552f0a14a63be7",
            "tar.gz"
        ),
        "nt": (
            "https://boostorg.jfrog.io/artifactory/main/release/1.78.0/source/boost_1_78_0.zip",
            "f22143b5528e081123c3c5ed437e92f648fe69748e95fa6e2bd41484e2986cc3",
            "zip"
        ),
    }[os.name]
    # Get + checksum
    print('Downloading boost headers...')
    hasher = hashlib.sha256()
    fd, comp_f = tempfile.mkstemp(suffix='.' + ext)
    with os.fdopen(fd, "wb") as f:
        with requests.get(url, allow_redirects=True, stream=True) as r:
            r.raise_for_status()
            for block in r.iter_content(chunk_size=2**16):
                hasher.update(block)
                f.write(block)
    if hasher.hexdigest() != sha:
        raise RuntimeError("Downloaded boost headers hash failure!")
    # Extract
    print('Extracting boost headers...')
    raw_boost = tempfile.mkdtemp(suffix='.tmp')
    extract(raw_boost, comp_f, ext)
    os.remove(comp_f)
    # Move into place
    print('Installing boost headers...')
    uncomp = glob.glob(os.path.join(raw_boost, '*'))
    if len(uncomp) != 1:
        raise RuntimeError("Boost should decompress into a single directory.")
    shutil.rmtree(d['boost'], ignore_errors=True)
    os.rename(os.path.join(uncomp[0], 'boost'), d['boost'])
    # Cleanup
    print('Cleaning temporary files...')
    shutil.rmtree(raw_boost)


def build_native():
    ### Prep
    old_pwd = os.getcwd()
    if not os.path.exists(d["build"]):
        os.mkdir(d["build"])
    os.chdir(d["build"])

    ### CMake
    print("Configuring...")
    info_file = os.path.join(d["build"], "for_setup_py.txt")
    cmake_args = cmake_config_args(info_file, claricpp)
    run_cmd_no_fail(find_exe("cmake"), *cmake_args, d["native"])
    info = parse_info_file(info_file)

    ### Generator
    generator = info["CMAKE_MAKE_PROGRAM"]
    is_make = generator.endswith("make")
    makej = [generator]  # TODO: test on windows; angr uses nmake /f Makefile-win
    try:
        if makej[0].endswith("make"):
            ncores = cpu_count() - 1
            if ncores < 1:
                ncores = 1
            makej.append("-j" + str(ncores))
    except NotImplementedError:
        pass

    ### Build claricpp
    print("Building " + claricpp + "...")
    run_cmd_no_fail(*makej, claricpp)

    ### Build API
    print("Building " + claricpp + "FFI API...")
    cdefs_intermediate_f = (
        info["CDEFS_SOURCE_F"] + ".i"
    )  # We care about the intermediate file
    # Make targets for intermediate files are relative to the build dir
    cdefs_target = os.path.relpath(cdefs_intermediate_f, d["build"])
    # Make works, not sure about other generators
    if not is_make:
        print(
            "Unknown if non-make generators support intermediate file targets",
            file=sys.stderr,
        )
    run_cmd_no_fail(*makej, cdefs_target)
    # Include dirs for building ffi
    inc_guess = (
        "/include/python"
        + str(sys.version_info.major)
        + "."
        + str(sys.version_info.minor)
    )
    include_dirs = inc_guess + ";" + info["Python_INCLUDE_DIRS"]
    # Run build_ffi
    sys.path.append(d["native"])
    from build_ffi import build_ffi_wrapper

    sys.path.pop()
    build_ffi_wrapper(
        input_lib=claricpp,
        output_lib=claricpp_ffi,
        build_dir=d["build"],
        ffi_dir=d["ffi"],
        intermediate_f=cdefs_intermediate_f,
        include_dirs=include_dirs,
        verbose=True,
    )

    ### Move files into place
    print("Moving files libs into place")
    shutil.copy2(find_lib(d["build"], "lib" + claricpp), d["lib"])
    shutil.copy2(find_lib(d["ffi"], claricpp_ffi), d["lib"])

    ### Cleanup
    os.chdir(old_pwd)


def clean_native():
    def rm_lib(name):
        where = find_lib(d["lib"], name, allow_missing=True)
        if where is not None:
            os.remove(where)
    rm_lib("lib" + claricpp)
    rm_lib(claricpp_ffi)
    shutil.rmtree(d["build"], ignore_errors=True)
    # Libs
    shutil.rmtree(d["boost"], ignore_errors=True)
    shutil.rmtree(d["z3"], ignore_errors=True)


######################################################################
#                             setuptools                             #
######################################################################


class sdist(_sdist):
    def run(self, *args):
        self.execute(lambda: get_boost(), (), msg="Getting boost headers")
        _sdist.run(self, *args)

class build(_build):
    def run(self, *args):
        if not os.path.exists(d['boost']): # No need to grab if they exist
            self.execute(lambda: get_boost(), (), msg="Getting boost headers")
        else:
            print('Using existing boost headers')
        self.execute(build_native, (), msg="Building claripy native")
        _build.run(self, *args)


class clean(_clean):
    def run(self, *args):
        self.execute(clean_native, (), msg="Cleaning claripy/native")
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
