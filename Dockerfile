# Use build.sh to build this in most circumstances
# If building directly, this is meant to be built with docker buildkit enabled:
#    export DOCKER_BUILDKIT=1
# Note that build arguments to this Dockerfile are not comprehensive w.r.t. all
# CMake options. Edit the CMake stage code directly to add or remove cmake
# options as desired.


##################################################
#                   Base Stage                   #
##################################################


FROM ubuntu:20.04 AS base
LABEL stage=base
SHELL [ "/bin/bash", "-ecux" ]

# Optional build args
ARG CXX_COMPILER="g++"
ARG INSTALL_OPTIONAL=0
ARG INSTALL_QOL_OPTIONAL=1

# Prep apt
ENV DEBIAN_FRONTEND=noninteractive
RUN apt-get update
RUN apt-get install -yq \
	python3 \
	gnupg2 \
	wget \
	git

# Install pip and prep python
RUN apt-get install -y python3-pip python3.8-venv
ENV VIRTUAL_ENV=/venv
RUN python3 -m venv "${VIRTUAL_ENV}"
ENV PATH="${VIRTUAL_ENV}/bin:${PATH}"
RUN pip3 install --upgrade pip

# Install required dependencies

# Native dependencies
RUN apt-get install -yq \
	"${CXX_COMPILER}" \
	make

# Python dependencies
# These are not necessary because of pip, however Z3 needs some CMake to build the wheel
# To avoid installing cmake twice I'm installing it from pip once before everything else
# Z3 does not declare native dependencies like cmake, even if they have pip packages :(

RUN pip3 install cmake # CMake (apt cmake is ancient) and z3 doesn't declare this as a pip dependency
RUN pip3 install wheel # Z3 fails to declare this as a dependency; TODO: PR a fix

# TODO: remove once Z3 fixes broken ELF header thing
RUN pip3 install z3-solver
RUN python3 -c 'import os, z3; lib=os.path.dirname(z3.__file__)+"/lib/libz3.so"; os.symlink(lib,lib+".4.8")'

# Optional depending on use build config

RUN if [[ "${INSTALL_OPTIONAL}" -ne 0 ]]; then \
	pip3 install clang-format; fi
RUN if [[ "${INSTALL_OPTIONAL}" -ne 0 ]]; then \
	apt-get install -yq \
		\
		`# Documentation` \
		graphviz \
		doxygen \
		\
		`# Static Analysis` \
		clang-tidy \
		cppcheck \
		iwyu \
		`# Dynamic Analysis` \
		valgrind \
	;fi

# Improved backtraces
RUN if [[ "${INSTALL_QOL_OPTIONAL}" -ne 0 ]]; then \
	apt-get install -yq libdw-dev; fi

# Avoid having pip install these during build stage. This makes debugging
# easier since testing doesn't require re-downloading / building wheels of
# dependencies (ex. z3 is very slow to build). These come from pyproject.toml
RUN if [[ "${INSTALL_QOL_OPTIONAL}" -ne 0 ]]; then \
	pip3 install \
		setuptools>=39.6.0 \
		z3-solver \
		requests \
		tqdm \
	;fi


##################################################
#                  Config Stage                  #
##################################################


FROM base AS config
LABEL stage=config

# Optional build arguments
# Note: VERBOSE must be empty to be off
ARG CTEST_OUTPUT_ON_FAILURE=1
ARG VERBOSE=""

# Constants
ENV CLARIPY="/claripy/" \
	VERBOSE="${VERBOSE}" \
	CTEST_OUTPUT_ON_FAILURE="${CTEST_OUTPUT_ON_FAILURE}"
ENV BUILD="${CLARIPY}/native/build/"

# Get source
RUN mkdir "${CLARIPY}"
COPY . "${CLARIPY}"
WORKDIR "${CLARIPY}"
RUN git submodule update --init --recursive

# Prune existing built objects
RUN python3 setup.py clean


##################################################
#                setup.py stages                 #
##################################################


# Let's test things individually
# If a setp fails, this makes debugging easier

FROM config as sdist
LABEL stage=sdist
RUN python setup.py sdist

FROM sdist as build
# Derive from sdist for speed
LABEL stage=build
RUN python setup.py build

FROM build as bdist_wheel
LABEL stage=bdist_wheel
RUN python setup.py bdist_wheel

FROM build as install
LABEL stage=install
RUN pip3 install --no-build-isolation --verbose .

FROM sdist as build_tests
# Derive from sdist for speed
LABEL stage=build_tests
RUN python setup.py build_tests


##################################################
#                   Test Stage                   #
##################################################


FROM build_tests as test
LABEL stage=test

# Test
RUN cd "${BUILD}" && ctest .


##################################################
#                   Docs Stage                   #
##################################################


FROM build_tests as docs
LABEL stage=docs

# TODO: fix me
RUN echo "TODO: Have setup.py provide an env var to toggle doc target"; \
	echo "Then verify INSTALL_OPTIONAL is true (i.e. doxygen is installed)"; \
	exit 1

# Make docs
RUN "${BUILD}" && make -j "$(("$(nproc)"-1))" docs
