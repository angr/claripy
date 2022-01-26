from distutils.command.build import build as _build
from distutils.command.clean import clean as _clean
from multiprocessing import cpu_count
import subprocess
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


def find_z3_include_dir():
    import z3

    base = os.path.dirname(z3.__file__)
    return os.path.join(base, "include")


def cmake_config_args(out_file, claricpp, z3_include_dir):
    # Config
    raw_config = {
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
        # So that python can access cmake data
        "FOR_SETUP_PY_F": out_file,
        # Z3 config
        "Z3_INCLUDE_PATH": z3_include_dir,
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


def find_exe(name):
    exe = shutil.which(name, mode=os.X_OK)
    if exe is None:
        raise RuntimeError("Cannot find " + name)
    return exe


def parse_info(info_file):
    with open(info_file) as f:
        data = f.readlines()
    data = [i.split("=", 1) for i in data if len(i.strip()) > 0]
    return {i[0].strip(): i[1].strip() for i in data}


def run_cmd_no_fail(*args):
    args = list(args)
    print("Running: subprocess.run(" + str(args) + ")")
    rc = subprocess.run(args)
    if rc.returncode != 0:
        what = os.path.basename(args[0])
        raise RuntimeError(what + " failed with return code: " + str(rc.returncode))
    return rc


def find_lib(base, name):
    files = glob.iglob(os.path.join(base, name + "*.*"))
    files = [
        i
        for i in files
        if (i.endswith(".so") or i.endswith(".dylib") or i.endswith(".dll"))
    ]
    if len(files) != 1:
        print("Found: " + str(files))
        raise RuntimeError("Could not find definitive lib: " + name + " in ", base)
    return files[0]


def mk_dirs(root):
    """
    Returns a dict of paths
    This is used for consistency
    ffi will be within build
    lib contains other files and already exists
    """
    native_dir = os.path.join(os.getcwd(), "native")
    build_dir = os.path.join(native_dir, "build")
    ret = {
        "native": native_dir,
        "build": build_dir,
        "ffi": os.path.join(build_dir, "ffi"),
        "lib": os.path.join(root, "claripy/claricpp"),
    }
    assert os.path.isdir(ret["lib"]), "Claripy directory is missing " + ret["lib"]
    return ret


def _build_native():
    ### Prep
    old_pwd = os.getcwd()
    d = mk_dirs(old_pwd)
    if not os.path.exists(d["build"]):
        os.mkdir(d["build"])
    os.chdir(d["build"])

    ### CMake
    print("Configuring...")
    info_file = os.path.join(d["build"], "for_setup_py.txt")
    cmake_args = cmake_config_args(info_file, claricpp, find_z3_include_dir())
    run_cmd_no_fail(find_exe("cmake"), *cmake_args, d["native"])
    info = parse_info(info_file)

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
    print(find_lib(d["build"], "lib" + claricpp), d["lib"])
    shutil.copy2(find_lib(d["build"], "lib" + claricpp), d["lib"])
    print(find_lib(d["ffi"], claricpp_ffi), d["lib"])
    shutil.copy2(find_lib(d["ffi"], claricpp_ffi), d["lib"])

    ### Cleanup
    os.chdir(old_pwd)


def _clean_native():
    d = mk_dirs(os.getcwd())
    os.remove(find_lib(d["lib"], "lib" + claricpp))
    os.remove(find_lib(d["lib"], claricpp_ffi))
    shutil.rmtree(d["build"], ignore_errors=True)


class build(_build):
    def run(self, *args):
        self.execute(_build_native, (), msg="Building claripy native")
        _build.run(self, *args)


class clean(_clean):
    def run(self, *args):
        self.execute(_clean_native, (), msg="Cleaning claripy native")
        _clean.run(self, *args)


cmdclass = {"build": build, "clean": clean}

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
    ],
    description="An abstraction layer for constraint solvers",
    url="https://github.com/angr/claripy",
    cmdclass=cmdclass,
    include_package_data=True,
    package_data={"claripy": ["claricpp/*"]},
)
