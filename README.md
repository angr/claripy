# claripy
[![Latest Release](https://img.shields.io/pypi/v/claripy.svg)](https://pypi.python.org/pypi/claripy/)
[![Python Version](https://img.shields.io/pypi/pyversions/claripy)](https://pypi.python.org/pypi/claripy/)
[![PyPI Statistics](https://img.shields.io/pypi/dm/claripy.svg)](https://pypistats.org/packages/claripy)
[![License](https://img.shields.io/github/license/angr/claripy.svg)](https://github.com/angr/claripy/blob/master/LICENSE)

Claripy is an abstracted constraint-solving wrapper.

## Project Links
Project repository: https://github.com/angr/claripy

Documentation: https://api.angr.io/projects/claripy/en/latest/

## Usage

It is usable!

General usage is similar to Z3:

```python
>>> import claripy
>>> a = claripy.BVV(3, 32)
>>> b = claripy.BVS('var_b', 32)
>>> s = claripy.Solver()
>>> s.add(b > a)
>>> print(s.eval(b, 1)[0])
```
