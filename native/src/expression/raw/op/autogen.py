'''@file
@brief This file is used to autogenerate op subclasses
This file *will* overwrite existing files

Within the defined io directory there must exist a config json file.
The config file will contain a list of dicts, each containing three things:
{
    'file' : <file_path>,
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
autogen_dir = os.path.join(io_dir, 'autogen')
io_dir = os.path.realpath('.')
op_dir = os.path.realpath('.')

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
    assert(os.path.exists(f), what + ' does not exist')

def template_replace(inp, cmd, replace_with):
    assert('_' not in cmd, 'No underscores allowed in cmd')
    cmd = '__' + cmd.upper()
    assert(cmd in inp, 'template_replace replace failed given cmd: ' + cmd)
    return inp.replace(cmd, replace_with)

# Generation functions


def generate_header(file, op, args, header_files):
    output_fname = os.path.join(output_dir, file)
    header_files.append(output_fname)
    # Construct prefix and suffix
    # Create body
    # TODO: also have to handle op namespace etc

    # Write out
    output = templates['prefix_and_suffix.hpp']
    output = template_replace(output, 'body', body)
    output = template_replace(output, 'upperop', op.upper())
    opinclude = os.path.relpath(os.path.join(op_dir, file), autogen_dir)
    output = template_replace(output, 'opinclude', opinclude)
    write_file(output_fname, output)

def generate_source(file, op, args, source_files):
    file = file[:-4] + '.cpp'
    source_files.append(file)
    # Create prefix

    # TODO:

    # Write out
    output = prefix + '\n\n' + body
    write_file(output_fname, output)

def generate_autogen(files):
    body = '\n'.join([ '#include "' + i + '"' for i in files ])
    output = template_replace(templates['autogen.hpp'], 'body', body)
    write_file(autogenhpp, output)

def generate_sources_out(files):
    prefix = os.path.relpath(autogen_dir, io_dir)
    output = '\n'.join([os.path.join(prefix, i) for i in files])
    write_file(sources_out, output)


# Other functions


def verify_config(config):
    assert(type(config) == list, 'Config must have a list type')
    # Entry verification
    for entry in config:
        assert(type(entry) == dict, 'Config entry of improper type')
        assert(set(entry.keys()) == ['file', 'op', 'args'], 'Config entry has improper keys')
        # File verification
        assert(type(config['file']) == str, 'Config entry["file"] should be of type str')
        assert(config['file'].endswith('.hpp'), 'Config entry["file"] must be an hpp file')
        assert(os.path.basename(config['file']) == config['file']),
            'Config entry["file"] must be the file basename')
        assert(os.path.exists(os.path.exists(os.path.join(input_dir, config['file'])),
            'Config entry["file"] does not exist');
        # Op verification
        assert(type(config['op']) == str, 'Config entry["op"] should be of type str')
        # Args verification
        assert(type(config['args']) == list, 'Config entry["file"] should be of type list')
        for i in config['args']:
            assert(type(i) == str, 'Config entry["file"] entry should be of type str')

def load_templates():
    global templates
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
    for i in tempalte_files:
        with open(os.path.join(templates_dir, i)) as f:
            data = f.read()
        templates[i.split('.in')[0]] = data

def main():
    # Error checking
    assert_exists(io_dir, 'io_dir')
    assert_exists(op_dir, 'op_dir')
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
        generate_header(**entry, header_files)
        generate_source(**entry, source_files)
    # Generate op.hpp
    generate_autogen(header_files)
    generate_sources_out(source_files)


# Don't run on import
if __name__ == '__main__':
    main()
