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

## Build System

The build system is cmake.

## Building

A `build.sh` script is provided that will build the Dockerfile. Building outside of the dockerfile is also quite possible as long as dependencies are installed.

### Docker

A dockerfile is provided which:
1. Uses clang-format replacement
2. Builds the shared object
3. Builds documentation

### CMake

Build configuration is done via cmake. CMake is currently configured with the following capabilities:
1. Static Analysis
2. Build documentation
3. Build test cases
4. Miscellaneous

The top level `CMakeLists.txt` file has many configurable options in it that affect the build.

### CTest

CTest is used for testing. After executing the cmake script, `make all`, or `make`, or `make test` should build the test cases. Execute `ctest .` in the build directory to run the test cases. For verbose mode, run `cmake --verbose .`.
