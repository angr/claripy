#!/usr/bin/env python3

from collections import defaultdict
from cffi import FFI
import argparse
import sys
import os


callbacks = """
extern "Python" void claripy_log(PyStr, const ClaricppLogLvl, PyStr);
extern "Python" ClaricppLogLvl claripy_level(PyStr);
extern "Python" ClaricppExpr claripy_simplify(const ClaricppExpr);
"""

# Helper functions


def log(add=""):
    """
    Adds data to an internal log
    Returns the internal log
    """
    log.log += "\n" + add
    return log.log


log.log = ""


def one_line_delims(inp, pairs):
    """
    Any newlines found between any pair of delimiters are replaced by spaces
    The result is returned, inp is not modified
    """
    assert type(inp) == str, "inp must be a str"
    weighted_pairs = {**{i: 1 for i, _ in pairs}, **{k: -1 for _, k in pairs}}
    adj = defaultdict(lambda: 0, weighted_pairs)
    out = ""
    count = 0
    for i in inp:
        count = count + adj[i]
        assert count >= 0, "Too many closing items!" + out
        out = out + (" " if (count > 0 and i == "\n") else i)
    assert count == 0, "Too many opening items!"
    return out


def condense(inp, allowed_endings):
    """
    Any lines not ending in an allowed ending are have the following newlines replaced by a space
    The result is returned, inp is not modified
    """
    assert type(inp) == str, "inp must be a str"
    lines = inp.split("\n")
    assert len(lines) > 1, "Input is too short"
    out = lines[0]
    assert len(out) > 0, "lines contains empty lines"
    for l in lines[1:]:
        out = out + ("\n" if out[-1] in allowed_endings else " ") + l
    return out.strip()


# Main functions


def get_source_f(native_dir):
    """
    Returns native/src/api.h
    """
    log("Extracting source...")
    # Sanity check
    native_dir = os.path.realpath(native_dir)
    assert os.path.exists(native_dir), "Native dir does not exist: " + native_dir
    assert os.path.isdir(native_dir), "Native dir is not a dir: " + native_dir
    src_dir = os.path.join(native_dir, "src")
    assert os.path.exists(src_dir), "Source dir is missing src directory"
    assert os.path.isdir(src_dir), "src is not a directory"
    # Processed source
    source_f = os.path.join(src_dir, "api.h")
    assert os.path.exists(source_f), "Source file does not exist: " + source_f
    assert os.path.isfile(source_f), "Source file is not a file: " + source_f
    return source_f


def get_processed_source_f(build_dir, intermediate_f):
    """
    Returns the preprocessor expanded version of native/src/api.h
    """
    # Sanity check
    assert os.path.exists(build_dir), "Build dir does not exist: " + build_dir
    assert os.path.isdir(build_dir), "Build dir is not a dir: " + build_dir
    cache_file = os.path.join(build_dir, "CMakeCache.txt")
    assert os.path.exists(
        cache_file
    ), "Build dir has not had CMake run in it. Cache file missing!"
    assert os.path.isfile(cache_file), "Cache file not a file"
    # Processed source
    psf = os.path.join(build_dir, "CMakeFiles/claricpp.dir/" + intermediate_f)
    assert os.path.exists(psf), "Processed source file does not exist: " + psf
    assert os.path.isfile(psf), "Processed source file is not a file: " + psf
    return psf


def get_cdefs(build_dir, intermediate_f):
    """
    Returns the cdefs python needs to use
    """
    log("Extracting cdefs...")
    with open(get_processed_source_f(build_dir, intermediate_f)) as f:
        raw_source = f.read()
    # Delete non-code
    lines = [i.strip() for i in raw_source.split("\n")]
    lines = [i for i in lines if len(i) > 0 and not i.startswith("#")]
    # Delete undesired
    both = "\n".join(lines).split("ClaricppFFIStart")
    assert len(both) == 2, "Too many start points"
    source = both[1][1 + both[1].find(";") :].strip()  # Ignore before start
    assert len(source) > 0, "ClaricppFFIStart at end"
    # String check
    assert not '"' in source, "String detected in source, parsing unspported"
    assert not "'" in source, "Char detected in source, parsing unspported"
    # Cleanup source
    source = one_line_delims(source, ["{}", "()"])
    source = source.replace(";;", ";").replace("  ", " ")
    cdefs = condense(source, ";}").strip()
    # Add callbacks
    cdefs = cdefs + "\n" + callbacks.strip()
    return cdefs


def build_ffi(lib_name, build_dir, intermediate_f, verbose, include_dirs):
    """
    Build lib_name
    """
    assert len(build_dir) > 0, "Build dir argument is empty"
    log("Building: " + lib_name)
    log("Build dir: " + build_dir)
    log("Intermediate_f: " + intermediate_f)
    log("Include_dir: " + str(include_dirs))
    build_dir = os.path.realpath(build_dir)
    # Extract data
    source_f = get_source_f(os.path.dirname(__file__))
    cdefs = get_cdefs(build_dir, intermediate_f)
    # Output dir
    log("Making output dir...")
    ffi_tmp = os.path.join(build_dir, "ffi")
    if not os.path.exists(ffi_tmp):
        os.mkdir(ffi_tmp)
    log("Writing out cdefs...")
    with open(os.path.join(ffi_tmp, "cdefs.txt"), "w") as f:
        f.write(cdefs)
    # Include directories
    inc_dir = []
    if include_dirs is not None:
        for i in ";".split(include_dirs):
            i = os.path.abspath(i)
            if os.path.exists(i):
                if os.path.isdir(i):
                    inc_dir.append(i)
        log("Directories to include: " + str(inc_dir))
    # FFI
    log("FFI config...")
    ffibuilder = FFI()
    ffibuilder.cdef(cdefs)
    ffibuilder.set_source(
        lib_name,
        '#include "' + source_f + '"',
        include_dirs=inc_dir,
        libraries=["claricpp"],
        library_dirs=[build_dir],
        extra_link_args=["-Wl,-rpath," + build_dir],
    )
    # Compile
    log("FFI compiling...")
    ffibuilder.compile(tmpdir=ffi_tmp, verbose=verbose)


def parse_args(prog, *args):
    """
    Parses arguments
    """
    parser = argparse.ArgumentParser(prog=os.path.basename(prog))
    parser.add_argument(
        "build_dir", type=str, help="The build directory where CMake ran."
    )
    parser.add_argument(
        "intermediate_f", type=str, help="The intermediate file to parse cdefs from."
    )  # src/ffi.cpp.i
    parser.add_argument(
        "--lib_name",
        "-o",
        type=str,
        default="claricpp_ffi",
        help="The output library name.",
    )
    parser.add_argument(
        "--verbose",
        "-v",
        action="store_true",
        help="If the compilation should be verbose.",
    )
    parser.add_argument(
        "--include_dirs",
        "-I",
        type=str,
        default=None,
        help="A ;-separated list of possible python include directories",
    )
    return parser.parse_args(args)


def main(argv):
    """
    Main function
    """
    try:
        ns = parse_args(*argv)
        return build_ffi(**vars(ns))
    except:
        print("\nPrinting log:\n" + log().strip(), file=sys.stderr)
        raise


# Don't run on import
if __name__ == "__main__":
    rv = main(sys.argv)
    if type(rv) is int:
        sys.exit(rv)
