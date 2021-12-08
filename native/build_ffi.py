#!/usr/bin/env python3

from collections import defaultdict
from cffi import FFI
import argparse
import sys
import os

# Helper functions

def one_line_delims(inp, pairs):
    '''
    Any newlines found between any pair of delimiters are replaced by spaces
    The result is returned, inp is not modified
    '''
    assert type(inp) == str, 'inp must be a str'
    adj = defaultdict(lambda: 0, { i:1 for i,_ in pairs } | { k:-1 for _,k in pairs })
    out = ''
    count = 0
    for i in inp:
        count = count + adj[i]
        assert count >= 0, 'Too many closing items!' + out
        out = out + (' ' if (count > 0 and i == '\n') else i)
    assert count == 0, 'Too many opening items!'
    return out

def condense(inp, allowed_endings):
    '''
    Any lines not ending in an allowed ending are have the following newlines replaced by a space
    The result is returned, inp is not modified
    '''
    assert type(inp) == str, 'inp must be a str'
    lines = inp.split('\n')
    assert len(lines) > 1, 'Input is too short'
    out = lines[0]
    assert len(out) > 0, 'lines contains empty lines'
    for l in lines[1:]:
        out = out + ('\n' if out[-1] in allowed_endings else ' ') + l
    return out.strip()

# Main functions

def get_source_f(native_dir):
    '''
    Returns native/src/api.h
    '''
    # Sanity check
    native_dir = os.path.realpath(native_dir)
    assert os.path.exists(native_dir), 'Native dir does not exist: ' + native_dir
    assert os.path.isdir(native_dir), 'Native dir is not a dir: ' + native_dir
    src_dir = os.path.join(native_dir, 'src')
    assert os.path.exists(src_dir), 'Source dir is missing src directory'
    assert os.path.isdir(src_dir), 'src is not a directory'
    # Processed source
    source_f = os.path.join(src_dir, 'api.h')
    assert os.path.exists(source_f), 'Source file does not exist: ' + source_f
    assert os.path.isfile(source_f), 'Source file is not a file: ' + source_f
    return source_f

def get_processed_source_f(build_dir):
    '''
    Returns the preprocessor expanded version of native/src/api.h
    '''
    # Sanity check
    assert os.path.exists(build_dir), 'Build dir does not exist: ' + build_dir
    assert os.path.isdir(build_dir), 'Build dir is not a dir: ' + build_dir
    cache_file = os.path.join(build_dir, 'CMakeCache.txt')
    assert os.path.exists(cache_file), 'Build dir has not had CMake run in it. Cache file missing!'
    assert os.path.isfile(cache_file), 'Cache file not a file'
    # Processed source
    psf = os.path.join(build_dir, 'CMakeFiles/claricpp.dir/src/ffi.cpp.i')
    assert os.path.exists(psf), 'Processed source file does not exist: ' + psf
    assert os.path.isfile(psf), 'Processed source file is not a file: ' + psf
    return psf

def get_cdefs(build_dir):
    '''
    Returns the cdefs python needs to use
    '''
    with open(get_processed_source_f(build_dir)) as f:
        raw_source = f.read()
    # Delete non-code
    lines = [ i.strip() for i in raw_source.split('\n') ]
    lines = [ i for i in lines if len(i) > 0 and not i.startswith('#') ]
    # Delete undesired
    both = '\n'.join(lines).split('ClaricppFFIStart')
    assert len(both) == 2, 'Too many start points'
    source = both[1][1 + both[1].find(';'):].strip() # Ignore before start
    assert len(source) > 0, 'ClaricppFFIStart at end'
    # String check
    assert not '"' in source, 'String detected in source, parsing unspported'
    assert not "'" in source, 'Char detected in source, parsing unspported'
    # Cleanup source
    source = one_line_delims(source, ['{}', '()'])
    source = source.replace(';;', ';').replace('  ', ' ')
    cdefs = condense(source, ';}')
    return cdefs

def build_ffi(lib_name, build_dir):
    '''
    Build lib_name
    '''
    build_dir = os.path.realpath(build_dir)
    # Extract data
    source_f = get_source_f(os.path.dirname(__file__))
    cdefs = get_cdefs(build_dir)
    # FFI
    ffibuilder = FFI()
    ffibuilder.cdef(cdefs)
    include = '#include "' + source_f + '"'
    ffibuilder.set_source(lib_name, include, libraries=['claricpp'], library_dirs=[build_dir], extra_link_args=['-Wl,-rpath,' + build_dir],
    )
    # Compile
    ffi_tmp = os.path.join(build_dir, 'ffi')
    if not os.path.exists(ffi_tmp):
        os.mkdir(ffi_tmp)
    ffibuilder.compile(tmpdir=ffi_tmp, verbose=True)

def parse_args(prog, *args):
    '''
    Parses arguments
    '''
    parser = argparse.ArgumentParser(prog=os.path.basename(prog))
    parser.add_argument('build_dir', type=str, help='The build directory where CMake ran.')
    parser.add_argument('--lib_name', '-o', type=str, help='The output library name.', default='claricpp_ffi')
    return parser.parse_args(args)

def main(argv):
    '''
    Main function
    '''
    ns = parse_args(*argv)
    return build_ffi(**vars(ns))

# Don't run on import
if __name__ == '__main__':
    rv = main(sys.argv)
    if type(rv) is int:
        sys.exit(rv)
