from distutils.core import setup

setup(
    name='claripy',
    version='0.9.0',
    packages=['claripy', 'claripy.backends', 'claripy.frontends', 'claripy.vsa', 'claripy.ast'],
    install_requires=[
        'ana',
        'z3',
    ],
    dependency_links=[
        'git+https://github.com/zardus/ana.git#egg=ana-0.1',
        'https://github.com/zardus/z3/archive/pypy-and-setup.zip#egg=z3-0.1',
    ],
)
