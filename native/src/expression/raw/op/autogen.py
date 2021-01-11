'''@file
@brief This file is used to autogenerate op subclasses
This file *will* overwrite existing files

Within the defined io directory there must exist a config json file.
The config file will contain a list of dicts, each containing three things:
{
    'file' : <filename>, # Must be a file in io_dir
    'op' : <op name>,
    'args' : <a list of unnamed argument types>
}
These entries will be used to autogenerate, in the autogen_dir,
a set of files that contain the necessary subclasses of op,
along with shared pointer aliases to each as needed.

Additionally generates autogen.hpp in io_dir

Finally prints out a relative path to each new source to sources_out in io_dir
'''

import argparse
import json
import sys
import os


# Filesystem Constants
io_dir = os.path.realpath('.')
autogen_dir = os.path.join(io_dir, 'autogen')

# Input Constants
config_f =    os.path.join(io_dir, 'autogen.json')
templates_dir = os.path.join(autogen_dir, 'templates')

# Output Constants
autogenhpp =  os.path.join(io_dir, 'autogen.hpp')
sources_out = os.path.join(io_dir, 'sources.txt')

# Globals
templates = {}


# Helper functions


def write_file(fname, output):
    print('Writing out ' + fname + '...')
    with open(fname, 'w') as f:
        f.write(output)

def assert_exists(f, what):
    assert os.path.exists(f), what + ' does not exist'

def template_replace(inp, cmd, replace_with):
    # Replace '__' + cmd.upper() with replace_with in inp (plus error checking)
    assert '_' not in cmd, 'No underscores allowed in cmd'
    cmd = '__' + cmd.upper()
    assert cmd in inp, 'template_replace replace failed given cmd: ' + cmd
    return inp.replace(cmd, replace_with)

def from_template(name, dct):
    ret = templates['type_op.hpp']
    for i,k in dct.items():
        ret = template_replace(ret, i, k)
    return ret

# Helper Generation Functions

def typeop(t, o, s1, s2):
    return from_template('type_op.hpp', {
        'type' : t,
        'op' : o,
        'super1' : s1,
        'super2' : s2
    })

def asto(s, t, o, sup):
    return from_template('abstract_sym_type_op.hpp', {
        'super2' : sup,
        'sym' : s,
        'type' : t,
        'op' : o
    })

# Generation functions


def generate_header(header_files, *, file, op, args):
    output_fname = os.path.join(autogen_dir, file)
    header_files.append(output_fname)
    # Create TypeOps
    typeops = '\n'.join([
        '// Base' + op,
        typeop('Base', op, 'Type::Base', 'Op::' + op),
        '// Base op direct subclasses',
        typeop('Int', op, 'Type::Int', 'Base' + op),
        typeop('Bool', op, 'Type::Bool', 'Base' + op),
        typeop('Bits', op, 'Type::Bits', 'Base' + op),
        '// Bits op direct subclasses',
        typeop('String', op, 'Type::String', 'Bits' + op),
        typeop('FP', op, 'Type::FP', 'Bits' + op),
        typeop('VS', op, 'Type::VS', 'Bits' + op),
        typeop('BV', op, 'Type::BV', 'Bits' + op)
    ])
    # Create Abstract SymTypeOps
    abstract_sto = '\n'.join([
        '// Abstract Sym Type Ops',
        asto('Symbolic', 'Base', op, 'Symbolic'),
        asto('Concrete', 'Base', op, 'Concrete'),
        asto('Symbolic', 'Bits', op, 'SymbolicBase' + op),
        asto('Concrete', 'Bits', op, 'ConcreteBase' + op)
    ])
    # Create Instantiable SymTypeOps
    instantiable_sto = '\n'.join([

#TODO

    ])
    # Create body
    body = '\n\n'.join([typeops, abstract_sto, instantiable_sto])
    # Prefix and suffix
    opinclude = os.path.relpath(os.path.join(io_dir, file), autogen_dir)
    output = from_templates('prefix_and_suffix.hpp',
        'opinclude' : opinclude,
        'upperop', op.upper(),
        'body' : body,
        'op', op
    }
    # Write out
    write_file(output_fname, output)

def generate_source(source_files, *, file, op, args):
    output_fname = os.path.join(autogen_dir, file[:-4] + '.cpp')
    source_files.append(output_fname)
    # Create prefix

    # TODO:

    # Write out
    # write_file(output_fname, output)

def generate_autogen(files):
    body = '\n'.join([ '#include "' + i + '"' for i in files ])
    output = from_template('autogen.hpp', {'body' : body})
    write_file(autogenhpp, output)

def generate_sources_out(files):
    prefix = os.path.relpath(autogen_dir, io_dir)
    output = '\n'.join([os.path.join(i, prefix) for i in files])
    write_file(sources_out, output)


# Other functions


def verify_config(config):
    assert type(config) == list, 'Config must have a list type'
    # Entry verification
    for entry in config:
        assert type(entry) == dict, 'Config entry of improper type'
        assert set(entry.keys()) == set(['file', 'op', 'args']), 'Config entry has improper keys'
        # File verification
        assert type(entry['file']) == str, 'Config entry["file"] should be of type str'
        assert entry['file'].endswith('.hpp'), 'Config entry["file"] must be an hpp file'
        assert os.path.basename(entry['file']) == entry['file'], \
            'Config entry["file"] must be the file basename'
        assert os.path.exists(os.path.join(io_dir, entry['file'])), \
            'Config entry["file"] does not exist'
        # Op verification
        assert type(entry['op']) == str, 'Config entry["op"] should be of type str'
        # Args verification
        assert type(entry['args']) == list, 'Config entry["file"] should be of type list'
        for i in entry['args']:
            assert type(i) == str, 'Config entry["file"] entry should be of type str'

def load_templates():
    global templates
    # The template files to load
    tempalte_files = [
        'abstract_sym_type_op.cpp.in',
        'instantiable_sym_type_op.hpp.in',
        'type_op.cpp.in',
        'abstract_sym_type_op.hpp.in',
        'prefix_and_suffix.cpp.in',
        'type_op.hpp.in',
        'autogen.hpp.in',
        'prefix_and_suffix.hpp.in'
    ]
    # Load each template file
    for i in tempalte_files:
        # Read file
        path = os.path.join(templates_dir, i)
        assert_exists(path, 'template file: ' + i)
        with open(path) as f:
            data = f.readlines()
        # Ignore // comments
        data = ''.join([ i for i in data if not i.startswith('//') ])
        # Save template
        templates[i.split('.in')[0]] = data

def main():
    # Error checking
    assert_exists(io_dir, 'io_dir')
    assert_exists(autogen_dir, 'autogen_dir')
    assert_exists(config_f, 'autogen.json config file')
    assert_exists(templates_dir, 'templates_dir')
    # Verify config file
    with open(config_f) as f:
        config = f.read()
    config = json.loads(config)
    verify_config(config)
    # Load templates
    load_templates()
    # Init
    source_files = []
    header_files = []
    # Generate each file
    for entry in config:
        generate_header(header_files, **entry)
        generate_source(source_files, **entry)
    # Generate op.hpp
    generate_autogen(header_files)
    generate_sources_out(source_files)


# Don't run on import
if __name__ == '__main__':
    main()
