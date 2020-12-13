# Claricpp

The native components of claripy, primarily written in C++.

## Documentation

Provided via doxygen.
Integrated with cmake.
CMake custom configures `Doxyfile.in` then creates a make target used to build documentation.

## Static Analysis

Provided by cppcheck

## Coding Standards

Enforced by clang-format.

## Building

The build system is cmake / make.

## Docker

A dockerfile is provided which:
1. Uses clang-format replacement
1. Uses cppcheck for static analysis
1. Builds the shared object
1. Builds documentation
