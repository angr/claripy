from distutils.core import setup

setup(
    name='claripy',
    version='5.6.10.12',
    packages=['claripy', 'claripy.backends', 'claripy.frontends', 'claripy.vsa', 'claripy.ast', 'claripy.frontend_mixins'],
    install_requires=[
        'ana',
        'angr-only-z3-custom==9002',
    ],
    description='An abstraction layer for constraint solvers',
    url='https://github.com/angr/claripy',
)
