# Use build.sh to build this in most circumstances
# If building directly, this is meant to be built with docker buildkit enabled:
#    export DOCKER_BUILDKIT=1
# Note that build arguments to this Dockerfile are not comprehensive w.r.t. all
# CMake options. Edit the CMake stage code directly to add or remove cmake
# options as desired.


# Set this to base if no dev stuff is desired
# Set to base_dev_extras to also install optional packages
ARG BASE_STAGE=base_dev

# Set this to config_verbose if desired
ARG CONFIG_STAGE=config


##################################################
#                   Base Stages                  #
##################################################


FROM ubuntu:20.04 as base
LABEL stage=base
SHELL [ "/bin/bash", "-ecux" ]

# Optional build args
ARG CXX="g++"

# Prep apt
ENV DEBIAN_FRONTEND=noninteractive
RUN apt-get update

# Install pip and prep python
RUN apt-get install -yq python3-pip python3.8-venv
ENV VIRTUAL_ENV=/venv
RUN python3 -m venv "${VIRTUAL_ENV}"
ENV PATH="${VIRTUAL_ENV}/bin:${PATH}"
RUN pip3 install --upgrade pip

# Native dependencies
RUN apt-get install make "${CXX}"

# Dev mode stage
FROM base as base_dev
LABEL stage=base_dev
ENV DEV_MODE=1

# Improved backtraces
RUN apt-get install -yq libdw-dev

# Python dependencies
RUN pip3 install \
	'z3-solver>=4.8.15.0' \
	'setuptools>=39.6.0' \
	requests \
	wheel \
	cmake \
	tqdm

# Extras stage
FROM base_dev as base_dev_extras
LABEL stage=base_dev_extras
RUN pip3 install clang-format
RUN apt-get install -yq \
    \
    `# Documentation` \
    graphviz \
    doxygen \
    `# Improve Documentation` \
    clang \
    \
    `# Static Analysis` \
    clang-tidy \
    cppcheck \
    iwyu \
    `# Dynamic Analysis` \
    valgrind


##################################################
#                  Config Stage                  #
##################################################


FROM "${BASE_STAGE}" as config
LABEL stage=config

# Optional build arguments
ARG CTEST_OUTPUT_ON_FAILURE=1

# Constants
ENV CLARIPY="/claripy/" \
	CTEST_OUTPUT_ON_FAILURE="${CTEST_OUTPUT_ON_FAILURE}"
ENV BUILD="${CLARIPY}/native/build/"
ENV CXX="${CXX}"

# Get source
RUN mkdir "${CLARIPY}"
COPY . "${CLARIPY}"
WORKDIR "${CLARIPY}"

# Verbose config stage
FROM config as config_verbose
LABEL stage=config_verbose
ENV VERBOSE=1


##################################################
#              setup.py pip stages               #
##################################################


FROM "${CONFIG_STAGE}" as install
LABEL stage=install
RUN pip3 install --verbose .


##################################################
#              setup.py dev stages               #
##################################################


# Let's test things individually
# If a setp fails, this makes debugging easier
# All stages which derive from anything but clean do for only for speed

FROM "${CONFIG_STAGE}" as clean
LABEL stage=clean
RUN if [[ "${DEV_MODE}" -ne 1 ]]; then \
		echo "To run the python setup.py dev stages you must use the base_dev base stage" \
		exit 1; \
	fi
RUN python setup.py clean

FROM clean as sdist
LABEL stage=sdist
RUN python setup.py sdist

FROM sdist as build
LABEL stage=build
RUN python setup.py build

FROM build as bdist_wheel
LABEL stage=bdist_wheel
RUN python setup.py bdist_wheel

FROM sdist as build_debug
LABEL stage=build_debug
RUN python setup.py native --debug

FROM sdist as build_tests
LABEL stage=build_tests
RUN python setup.py native --tests --debug --no-api

FROM build_tests as test
LABEL stage=test
RUN python setup.py native --tests --debug --no-api --run-tests

FROM sdist as docs
LABEL stage=docs
# Dependencies; clang is optional improves output
RUN apt-get install -yq doxygen graphviz clang
RUN python setup.py native --docs --no-api --no-lib
