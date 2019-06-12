# claripy

Claripy is an abstracted constraint-solving wrapper.

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
