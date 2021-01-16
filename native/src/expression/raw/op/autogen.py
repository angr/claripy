'''@file
@brief This file is used to autogenerate op subclasses
@todo Handle std::forwarding for speed up
This file *will* overwrite existing files

Within the defined io directory there must exist a config json file.
The config file will contain a list of dicts, each containing three things:
{
    'file' : <filename>, # Must be a file in io_dir
    'op' : <op name>,
    'ctor_args' : <a list of unnamed argument types given to the constructor>
    'parents' : [] # A list of immediate superclasses, order should be the same as in the code
}
While it is not required, 'parents' will likely start with 'Op::Base'.

Optionally, the json entry may contain any or all of the following:
{
    # Default to [ 'Symbolic', 'Concrete' ]
    # Allows the user to declare a class only Symbolic, Concrete, or both, or none
    # Can contain only 'Symbolic', 'Concrete', both, or none
    # Warning, if none, no code is generated for this class, but super information is used for other classes!
    'soc' : <list>
}

These entries will be used to autogenerate, in the autogen_dir,
a set of files that contain the necessary subclasses of op,
along with shared pointer aliases to each as needed.

Additionally generates autogen.hpp in io_dir

Finally prints out a relative path to each new source to sources_out in io_dir
'''

from collections import defaultdict
import itertools
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
ctor_args = {
    'Base' : [ 'const Hash::Hash', 'std::vector<std::shared_ptr<Annotation::Base>> &' ],
    'CUSized' : [ 'Constants::UInt' ],
    'Symbolic' : [],
    'Concrete' : [],
    # Types
    'Type::Base' : [],
    'Type::Int' : [],
    'Type::Bool' : [],
    'Type::Bits' : [],
    'Type::String' : [],
    'Type::FP' : [],
    'Type::VS' : [],
    'Type::BV' : [],
    # Op
    'Op::Base' : []
}
parents = {
    # Only lists direct superclasses, list order should be the same as in the C++ code
    'Base' : [],
    'CUSized' : [],
    'Symbolic' : [ 'Base' ],
    'Concrete' : [ 'Base' ],
    # Types
    'Type::Base' : [ 'Base' ],
    'Type::Bool' : [ 'Type::Base' ],
    'Type::Int' :  [ 'Type::Base' ],
    'Type::Bits' : [ 'Type::Base', 'CUSized' ],
    'Type::String' : [ 'Type::Bits' ],
    'Type::BV' : [ 'Type::Bits' ],
    'Type::FP' : [ 'Type::Bits' ],
    'Type::VS' : [ 'Type::Bits' ],
    # Ops
    'Op::Base' : [ 'Base' ]
}
# Below are shortcuts, these classifications are not defined just by these
instantiable_types = [ 'Int', 'Bool', 'String', 'BV', 'FP', 'VS' ]
abstract_types = [ 'Base', 'Bits' ]
all_types = abstract_types + instantiable_types
symbolic_concrete = [ 'Symbolic', 'Concrete' ]
me = os.path.basename(sys.argv[0])


# Helper functions


def write_file(fname, output):
    print('-- \t' + fname)
    output = '\n'.join(i.rstrip() for i in output.split('\n')).strip()
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
    ret = templates[name]
    for i,k in dct.items():
        ret = template_replace(ret, i, k)
    return ret

def determinte_ctor_args_helper(me, pars, skip):
    global parents
    raw = []
    who = []
    for p in pars:
        if p not in skip:
            a, b = determinte_ctor_args_helper(p, parents[p], skip)
            if p not in skip:
                skip.add(p)
                raw.extend(a)
                who.extend(b)
    if me not in skip:
        my_args = ctor_args[me]
        raw.extend(my_args)
        qme = me if '::' in me else ('Raw::' + me)
        who.extend(itertools.repeat(qme, len(my_args)))
    return raw, who

def determinte_ctor_args(sym, typ, op, *, hpp):
    skip = sym + typ + op
    raw, who = determinte_ctor_args_helper(me, [sym, 'Type::' + typ, 'Op::' + op], set([me]))
    if hpp:
        return raw
    args = [ i + ' a' + str(n) for n,i in enumerate(raw) ]
    return list(zip(args, who))

def small_cpp_comment(what):
    return '\n// ' + what + '\n'

def big_cpp_comment(what):
    length = 70
    line = '/' + (length-2)*'*' + '/'
    mid = '/*' +  what.center(length-4, ' ') + '*/'
    return '\n' + '\n'.join([line, mid, line]) + '\n'


# Helper Generation Functions


def typeop(t, o, s1, s2):
    return from_template('type_op.hpp', {
        'type' : t,
        'op' : o,
        'super1' : s1,
        'super2' : s2
    })

def asto(s, t, o, s2):
    return from_template('abstract_sym_type_op.hpp', {
        'super2' : s2,
        'sym' : s,
        'type' : t,
        'op' : o
    })

def isto(s, t, o, s2):
    # Derive ctor args from arguments
    args = '\n\t\t' + ',\n\t\t'.join(determinte_ctor_args(s, t, o, hpp=True))
    # Return the constructed code
    return from_template('instantiable_sym_type_op.hpp', {
        'super2' : s2,
        'sym' : s,
        'type' : t,
        'op' : o,
        'ctorargs' : args
    })

def isto_cpp(sym, typ, op):
    # Derive ctor args from arguments
    args = determinte_ctor_args(sym, typ, op, hpp=False)
    # Constructor decl
    name = sym + typ + op
    declargs = [ i[0] for i in args ]
    decl = name + '::' + name + '(\n\t\t' + ',\n\t\t'.join(declargs) + ')'
    # Parents
    required_args = defaultdict(lambda : [])
    for a, who in args:
        required_args[who].append(a.split(' ')[-1])
    raw_base_args = args[:len(ctor_args['Base'])]
    parents = [ who + '(' + ', '.join(a) + ')' for who, a in required_args.items() ]
    # Return ctor code
    ctor = decl + '\n\t:\n\t' + ',\n\t'.join(parents) + '\n'
    return from_template('instantiable_sym_type_op.cpp', {
        'ctor' : ctor,
        'sym' : sym,
        'type' : typ,
        'op' : op
    })


# Generation functions


def generate_header(header_files, *, file, op, soc):
    output_fname = os.path.join(autogen_dir, file)
    header_files.append(output_fname)
    # Create TypeOps
    body = '\n\n'.join([
        big_cpp_comment('Base' + op),
        typeop('Base', op, 'Type::Base', 'Op::' + op),
        small_cpp_comment('Base' + op + ' direct subclasses'),
        typeop('Int', op, 'Type::Int', 'Base' + op),
        typeop('Bool', op, 'Type::Bool', 'Base' + op),
        typeop('Bits', op, 'Type::Bits', 'Base' + op),
        small_cpp_comment('Bits' + op + ' direct subclasses'),
        typeop('String', op, 'Type::String', 'Bits' + op),
        typeop('FP', op, 'Type::FP', 'Bits' + op),
        typeop('VS', op, 'Type::VS', 'Bits' + op),
        typeop('BV', op, 'Type::BV', 'Bits' + op)
    ])
    # For both symbolic and concrete as needed
    for sym in soc:
        # Create Abstract SymTypeOps
        abstract_sto = '\n\n'.join([
            big_cpp_comment('Abstract ' + sym + ' Type Ops'),
            asto(sym, 'Base', op, sym),
            asto(sym, 'Bits', op, sym + 'Base' + op),
        ])
        # Create Instantiable SymTypeOps
        instantiable_sto = '\n\n'.join([
            big_cpp_comment('Instantiable ' + sym + ' Type Ops'),
            small_cpp_comment('Base Subclasses'),
            isto(sym, 'Int', op, sym + 'Base' + op),
            isto(sym, 'Bool', op, sym + 'Base' + op),
            small_cpp_comment('Bits Subclasses'),
            isto(sym, 'String', op, sym + 'Bits' + op),
            isto(sym, 'FP', op, sym + 'Bits' + op),
            isto(sym, 'VS', op, sym + 'Bits' + op),
            isto(sym, 'BV', op, sym + 'Bits' + op)
        ])
        body = '\n\n'.join([body, abstract_sto, instantiable_sto])
    # Aliases
    aliases = [ big_cpp_comment('Create aliases for each raw type') + '\n' ]
    for typ in all_types:
        aliases.append(from_template('alias.hpp', {'name' : typ + op }))
        for sym in soc:
            aliases.append(from_template('alias.hpp', {'name' : sym + typ + op }))
    # Prefix and suffix
    opinclude = os.path.relpath(os.path.join(io_dir, file), autogen_dir)
    output = from_template('prefix_and_suffix.hpp', {
        'aliases' : '\n\t'.join(aliases),
        'opinclude' : opinclude,
        'upperop' : op.upper(),
        'body' : body.replace('\n', '\n\t\t\t'),
        'op' : op
    })
    # Write out
    write_file(output_fname, output)

def generate_source(header, source_files, *, file, op, soc):
    output_fname = os.path.join(autogen_dir, file[:-4] + '.cpp')
    source_files.append(output_fname)
    # Create TypeOps
    typeops = [
        from_template('type_op.cpp', { 'type' : typ, 'op' : op }) \
        for typ in all_types
    ]
    body = big_cpp_comment('TypeOp') + '\n\n' + '\n\n'.join(typeops)
    # For both symbolic and concrete as needed
    for sym in soc:
        # Abstract SymTypeOps
        abstract_sto = '\n\n'.join([
            big_cpp_comment('Abstract Sym Type Ops'),
            *[ from_template('abstract_sym_type_op.cpp', { 'sym' : sym, 'type' : typ, 'op' : op }) \
            for typ in abstract_types ]
        ])
        # Instantiable SymTypeOps
        instantiable_sto = '\n\n'.join([
            big_cpp_comment('Instantiable Sym Type Ops'),
            *[ isto_cpp(sym, typ, op) for typ in instantiable_types ]
        ])
        body = '\n\n'.join([body, abstract_sto, instantiable_sto])
    # Prefix and suffix
    output = from_template('prefix_and_suffix.cpp', {
        'autogeninclude' : os.path.basename(header),
        'body' : body
    })
    # Write out
    write_file(output_fname, output)

def generate_autogen(files):
    files = [ os.path.relpath(i, io_dir) for i in files ]
    body = '\n'.join([ '#include "' + i + '"' for i in files ])
    output = from_template('autogen.hpp', {'body' : body})
    write_file(autogenhpp, output)

def generate_sources_out(files):
    output = '\n'.join([os.path.relpath(i, io_dir) for i in files])
    write_file(sources_out, output)


# Other functions


def verify_config(config):
    assert type(config) == list, 'Config must have a list type'
    # Entry verification
    for entry in config:
        assert type(entry) == dict, 'Config entry of improper type'
        assert set(['file', 'op', 'ctor_args']).issubset(entry.keys()), \
            'Config entry requires file, op, and ctor_args'
        assert set(entry.keys()).issubset(['file', 'op', 'ctor_args', 'soc', 'parents']), \
            'Config entry has unknown keys'
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
        assert type(entry['ctor_args']) == list, 'Config entry["ctor_args"] should be of type list'
        for i in entry['ctor_args']:
            assert type(i) == str, 'Config entry["ctor_args"] item should be of type str'
        # Parents verification
        assert type(entry['parents']) == list, \
            'Config entry["parents"] should be of type list'
        for i in entry['parents']:
            assert type(i) == str, 'Config entry["parents"] item should be of type str'
        # Allow concrete or symbolic
        if 'soc' in entry:
            assert type(entry['soc']) == list, 'Config entry["soc"] must be a list'
            sym = set(['Symbolic'])
            con = set(['Concrete'])
            assert set(entry['soc']) in [ sym, con, sym | con ], \
                'Config entry["soc"] may only contain "Symbolic", "Concrete", or both.'

def verify_parents(queue=None):
    # This does not check for cycles !
    global parents
    if queue is None:
        queue = list(parents.keys())
    while len(queue) > 0:
        key = queue.pop()
        assert key in parents, 'Immediate superclass ' + key + ' is unknown'
        value = parents[key]
        if len(value) > 0:
            queue.extend(value)

def import_parents(config):
    global parents
    for entry in config:
        name = entry['op']
        assert name not in parents, name + ' exists in config more than once, or is reserved by autogen.py'
        parents['Op::' + name] = entry['parents']
        del entry['parents']
    verify_parents()

def import_ctor_args(config):
    global ctor_args
    for entry in config:
        name = entry['op']
        assert name not in ctor_args, name + ' exists in config more than once, or is reserved by autogen.py'
        ctor_args['Op::' + name] = entry['ctor_args']
        del entry['ctor_args']

def load_templates():
    global templates
    # The template files to load
    tempalte_files = [
        'prefix_and_suffix.cpp.in',
        'prefix_and_suffix.hpp.in',
        'type_op.hpp.in',
        'type_op.cpp.in',
        'abstract_sym_type_op.cpp.in',
        'abstract_sym_type_op.hpp.in',
        'instantiable_sym_type_op.hpp.in',
        'instantiable_sym_type_op.cpp.in',
        'autogen.hpp.in',
        'alias.hpp.in'
    ]
    # Load each template file
    for i in tempalte_files:
        # Read file
        path = os.path.join(templates_dir, i)
        assert_exists(path, 'template file: ' + i)
        with open(path) as f:
            data = f.readlines()
        # Ignore // comments
        data = ''.join([ i for i in data if not i.startswith('//') ]).strip()
        # Save template
        templates[i.split('.in')[0]] = data

def main():
    # Error checking
    print('-- Starting ' + me)
    assert_exists(io_dir, 'io_dir')
    assert_exists(autogen_dir, 'autogen_dir')
    assert_exists(config_f, 'autogen.json config file')
    assert_exists(templates_dir, 'templates_dir')
    # Load and verify config file
    print('-- Loading files')
    with open(config_f) as f:
        config = f.read()
    config = json.loads(config)
    verify_config(config)
    import_parents(config)
    import_ctor_args(config)
    # Add extra config
    for entry in config:
        if 'soc' not in entry:
            entry['soc'] = [ 'Symbolic', 'Concrete' ]
    # Load templates
    load_templates()
    print('-- Loading files - done')
    # Init
    source_files = []
    header_files = []
    # Generate each file
    print('-- Generating autogen files')
    for entry in config:
        generate_header(header_files, **entry)
        generate_source(header_files[-1], source_files, **entry)
    print('-- Generating autogen files - done')
    # Generate op.hpp
    print('-- Generating aggregation files')
    generate_autogen(header_files)
    generate_sources_out(source_files)
    print('-- Generating aggregation files - done')
    # Exit
    print('-- Completed ' + me)
    sys.exit(0)


# Don't run on import
if __name__ == '__main__':
    main()
