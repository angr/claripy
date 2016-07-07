# claripy

Claripy is a abstracted constraint-solving wrapper.

## Usage

It is usable!

General usage is similar to z3:

```python
>>> import claripy
>>> a = claripy.BVV(3, 32)
>>> b = claripy.BV('var_b', 32)
>>> s = claripy.Solver()
>>> s.add(b > a)
>>> print s.eval(b, 1)[0]
```
