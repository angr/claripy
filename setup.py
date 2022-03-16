import os

from setuptools import setup, find_packages

with open(os.path.join(os.path.dirname(__file__), 'VERSION')) as f:
    version = f.read().strip()

setup(
    name='claripy',
    version=version,
    python_requires='>=3.6',
    packages=packages,
    install_requires=[
        'z3-solver>=4.8.5.0',
        'future',
        'cachetools',
        'decorator',
        'pysmt>=0.9.1.dev119',
    ],
    description='An abstraction layer for constraint solvers',
    url='https://github.com/angr/claripy',
    package_data={
        'claripy': ["py.typed"]
    },
)
