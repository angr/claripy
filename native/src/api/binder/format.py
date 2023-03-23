from typing import Tuple, Dict, List, Set
from functools import reduce
from pathlib import Path
import argparse
import sys
import os
import re


prefix: str = """
#ifndef BINDER_PYBIND11_TYPE_CASTER
    #define BINDER_PYBIND11_TYPE_CASTER
    PYBIND11_DECLARE_HOLDER_TYPE(T, std::shared_ptr<T>)
    PYBIND11_DECLARE_HOLDER_TYPE(T, T*)
    PYBIND11_MAKE_OPAQUE(std::shared_ptr<void>)
#endif
""".strip()


def py_mod(name: str) -> str:
    return f"PYBIND11_MODULE({name}, root_module) {{"

def make_replacements(x: str, name: str, namespace: str) -> str:
    """
    Make replacements to clean up x
    """
    x = re.sub("PYBIND11_MODULE\\([a-zA-Z0-9_]+, root_module\\) {", py_mod(name), x)
    x = re.sub('root_module\\.doc\\(\\) = "[a-zA-Z0-9_]+ module"',
               f'root_module.doc() = "{name} module"', x)
    return x.replace("sub_modules {", 'sub_modules {\n\t\t{"", "API"},')


def _autogen(lines: List[str], name: str, namespace: str, includes: List[str]) -> str:
    """
    Generate the content of the autogenfile using lines as input
    """
    normal: Tuple[str, ...] = tuple(i for i in lines if not i.startswith("#include"))
    headers: str = "".join(set(i for i in lines if i not in normal))
    # Remove duplicate prefix-es
    seq: Tuple[str, ...] = tuple(i.strip() for i in prefix.split("\n"))
    stripped: Tuple[str, ...] = tuple(i.strip() for i in normal)
    indexes: Tuple[int, ...] = tuple(
        i for i in range(len(stripped)) if stripped[i : i + len(seq)] == seq
    )
    body: Tuple[str, ...] = (
        i
        for idx, i in enumerate(normal)
        if not any(idx >= k and idx < (k + len(seq)) for k in indexes)
    )
    # Edit code
    n3: str = "\n" * 3
    clean: str = "".join(make_replacements(i, name, namespace) for i in body)
    if namespace:
        delim: str = py_mod(name)
        top, bottom = clean.split(delim)
        bottom = bottom.replace("bind_", f"{namespace}::bind_")
        bottom = bottom.replace("ModuleGetter", f"{namespace}::ModuleGetter")
        clean = f"namespace {namespace} {{{n3}{top}{n3}}}{n3}{delim}{bottom}"
    clean = f'/** The name of the root module */\nCCSC API::root_mod_name {{ "{name}" }};{n3}{clean}'
    while n3 + "\n" in clean:
        clean = clean.replace(n3 + "\n", n3)
    # Manual bind
    body: List[str] = clean.rsplit("}", 1)
    assert len(body) == 2, "sanity check failed"
    clean = "\tAPI::bind_manual(root_module, M);\n}".join(body)
    # Finalize
    return n3.join((
            "\n".join(f'#include "{i}"' for i in includes),
            headers,
            prefix,
            clean,
    ))


def autogen(in_dir: Path, out_file: Path, name: str, **kwargs):
    out_file = out_file.resolve()
    in_dir = in_dir.resolve()
    assert in_dir.is_dir(), f"Input directory {in_dir} must exist"
    assert not out_file.exists(), f"Output file {out_file} must not exist"
    in_file: Path = (in_dir / f"{name}.cpp").resolve()
    assert in_file.is_file(), f"Input file {in_file} must exist"
    # Generate output file
    print(f"Loading {in_file}")
    with in_file.open("r") as f:
        lines: List[str] = f.readlines()
    print(f"Processing...")
    output: str = _autogen(lines, name, **kwargs).strip()
    print(f"Writing out {out_file}")
    with out_file.open("x") as f:
        f.write(output)


def parse_args(prog, *args):
    parser = argparse.ArgumentParser(prog=os.path.basename(prog))
    parser.add_argument("in_dir", type=Path, help="The input directory to process")
    parser.add_argument("out_file", type=Path, help="The output file location")
    parser.add_argument("name", type=str, help="The root module name")
    parser.add_argument("namespace", type=str, help="The binder code namespace")
    parser.add_argument(
        "includes",
        default=[],
        nargs="*",
        help="Additional includes to add to autogen.cpp",
    )
    return parser.parse_args(args)


def main(argv):
    ns = parse_args(*argv)
    return autogen(**vars(ns))


if __name__ == "__main__":
    main(sys.argv)
