try:
    from setuptools import setup
    from setuptools import find_packages
    packages = find_packages()
except ImportError:
    from distutils.core import setup
    import os
    packages = [x.strip('./').replace('/','.') for x in os.popen('find -name "__init__.py" | xargs -n1 dirname').read().strip().split('\n')]

if bytes is str:
    raise Exception("This module is designed for python 3 only. Please install an older version to use python 2.")

setup(
    name='claripy',
    version='8.20.6.1',
    python_requires='>=3.6',
    packages=packages,
    install_requires=[
        'z3-solver>=4.8.5.0',
        'future',
        'cachetools',
        'decorator',
        'pysmt',
    ],
    description='An abstraction layer for constraint solvers',
    url='https://github.com/angr/claripy',
)
