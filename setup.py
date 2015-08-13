from distutils.core import setup

setup(
    name='claripy',
    version='0.9.0.1',
    packages=['claripy', 'claripy.backends', 'claripy.frontends', 'claripy.vsa', 'claripy.ast'],
    install_requires=[
        'ana',
        'angr-z3',
    ],
)
