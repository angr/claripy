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
LABEL claricpp=base
SHELL [ "/bin/bash", "-ecux" ]

# Optional build args
ARG CXX_COMPILER="g++"
ARG Z3_HEADER_REL_PATH=""

# Prep apt
ENV DEBIAN_FRONTEND=noninteractive
RUN apt-get update
RUN apt-get install -yq \
	python3-pip \
	gnupg2 \
	wget

# Add extra repos as needed
RUN wget -O - 'https://apt.llvm.org/llvm-snapshot.gpg.key' | apt-key add -
RUN echo 'deb http://apt.llvm.org/focal/ llvm-toolchain-focal-11 main' >> /etc/apt/sources.list
RUN echo 'deb-src http://apt.llvm.org/focal/ llvm-toolchain-focal-11 main' >> /etc/apt/sources.list
RUN apt-get update

# Optional depending on use build config
# We install these first since they aren't dependent on build args

# Documentation
RUN apt-get install -yq \
	graphviz \
	doxygen

# Static Analysis
RUN apt-get install -yq \
	clang-format-11 \
	clang-tidy-11 \
	cppcheck \
	iwyu

# Dynamic Analysis
RUN apt-get install -yq \
	valgrind

# Install required dependencies

# Move args into env
ENV CXX_COMPILER="${CXX_COMPILER}"
ENV Z3_HEADER_REL_PATH="${Z3_HEADER_REL_PATH}"

# Build
RUN apt-get install -yq \
	"${CXX_COMPILER}" \
	make
RUN pip3 install cmake # apt cmake is old

# Z3
RUN test -n "${Z3_HEADER_REL_PATH}" && INST='z3' || INST='git'; \
	apt-get install -yq "${INST}"


##################################################
#                  Config Stage                  #
##################################################


FROM base AS config
LABEL claricpp=config

# Required build args
ARG VERSION=""
RUN test -n "${VERSION}"

# Optional build args
ARG FORMAT="False"

# Build constants
ENV CLARIPY="/claripy/"
ENV NATIVE="${CLARIPY}/native/"
ENV SRC="${NATIVE}/src/"
ENV BUILD="/build/"

# Copy in source files
COPY . "${NATIVE}"
RUN echo "${VERSION}" > "${CLARIPY}/VERSION"

# Optional clang-format
WORKDIR "${NATIVE}"
RUN if [[ "${FORMAT}" == True ]]; then \
		find . -regex '.*\.\(cpp\|hpp\)' -exec \
			clang-format-11 -style=file -i {} ';' ; \
	fi


##################################################
#                  CMake Stage                   #
##################################################


FROM config as cmake
LABEL claricpp=cmake

# Optional build args
ARG CMAKE_BUILD_TYPE="Debug"
ARG CMAKE_VERBOSE_MAKEFILE="OFF"
ARG NUM_CORES=1

# Move build args into env
ENV NUM_CORES="${NUM_CORES}"

# cd build
RUN mkdir "${BUILD}"
WORKDIR "${BUILD}"

# Create cmake command
ENV CMAKE_SH="${BUILD}/cmake.sh"
RUN echo \
	cmake \
		-DCMAKE_VERBOSE_MAKEFILE="${CMAKE_VERBOSE_MAKEFILE}" \
		-DCMAKE_BUILD_TYPE="${CMAKE_BUILD_TYPE}" \
		-DCMAKE_CXX_COMPILER="${CXX_COMPILER}" \
		-D"Z3_NUM_CORES"="${NUM_CORES}" \
	> "${CMAKE_SH}"
RUN if [ -n "${Z3_HEADER_REL_PATH}" ]; then \
	echo \
		"-DZ3_ACQUISITION_MODE=SYSTEM" \
		"-DZ3_INCLUDE_PATH=${NATIVE}/${Z3_HEADER_REL_PATH}" \
	>> "${CMAKE_SH}" \
	;fi
RUN echo "${NATIVE}" >> "${CMAKE_SH}"

# Fix whitespaces and make executable
RUN tr '\n' ' ' < "${CMAKE_SH}" > /tmp/cmake; \
	mv /tmp/cmake "${CMAKE_SH}"
RUN chmod +x "${CMAKE_SH}"

# CMake
RUN cat "${CMAKE_SH}"
RUN "${CMAKE_SH}"


##################################################
#                Acquire Z3 Stage                #
##################################################


FROM cmake as acquire_z3
LABEL claricpp=acquire_z3

# Make
RUN make z3

# Re-run CMake
# This step only matters if z3 acquisition mode is set to build
RUN "${CMAKE_SH}"


##################################################
#                  Build Stage                   #
##################################################


FROM acquire_z3 as build
LABEL claricpp=build

# Make
RUN make -j "${NUM_CORES}" claricpp


##################################################
#                Test Build Stage                #
##################################################


FROM build as test_build
LABEL claricpp=test_build

# Build the test cases
RUN make -j "${NUM_CORES}" all


##################################################
#                   Test Stage                   #
##################################################


FROM test_build as test
LABEL claricpp=test

# Optional build args
ARG VERBOSE_TEST="False"

# Test if make targets request it
RUN if [[ "${VERBOSE_TEST}" == True ]]; then \
		ctest --verbose -j "${NUM_CORES}" . ; \
	else \
		ctest -j "${NUM_CORES}" . ; \
	fi


##################################################
#                   Docs Stage                   #
##################################################


FROM test_build as docs
LABEL claricpp=docs

# Make docs
RUN make docs
