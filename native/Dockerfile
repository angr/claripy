##################################################
#                   Base Stage                   #
##################################################


FROM ubuntu:20.04 AS base
LABEL claricpp=base
SHELL [ "/bin/bash", "-ecux" ]

# Optional build args
ARG CXX_COMPILER=g++
RUN test -n "${CXX_COMPILER}"

# Move args into env
ENV CXX_COMPILER="${CXX_COMPILER}"

# Prep apt
ENV DEBIAN_FRONTEND=noninteractive
RUN apt-get update
RUN apt-get install -yq \
	gnupg2 \
	wget

# Add extra repos as needed
RUN wget -O - 'https://apt.llvm.org/llvm-snapshot.gpg.key' | apt-key add -
RUN echo 'deb http://apt.llvm.org/focal/ llvm-toolchain-focal-11 main' >> /etc/apt/sources.list
RUN echo 'deb-src http://apt.llvm.org/focal/ llvm-toolchain-focal-11 main' >> /etc/apt/sources.list
RUN apt-get update

# Install required dependencies

# Build
RUN apt-get install -yq \
	"${CXX_COMPILER}" \
	cmake \
	make
# Z3 build
RUN apt-get install -yq \
	python3-distutils \
	git
# Boost multiprecision with gmp backend for mpz frontend
RUN apt-get install -yq \
	libboost-dev \
	libgmp-dev

# Optional depending on use build config

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

# cd build
RUN mkdir "${BUILD}"
WORKDIR "${BUILD}"

# CMake
RUN cmake \
	-DCMAKE_VERBOSE_MAKEFILE="${CMAKE_VERBOSE_MAKEFILE}" \
	-DCMAKE_BUILD_TYPE="${CMAKE_BUILD_TYPE}" \
	-DCMAKE_CXX_COMPILER="${CXX_COMPILER}" \
	"${NATIVE}"


##################################################
#                  Build Stage                   #
##################################################


FROM cmake as build
LABEL claricpp=build

# Optional build arg
ARG NUM_CORES=1
RUN test -n "${NUM_CORES}"

# Move build args into env
ENV NUM_CORES="${NUM_CORES}"

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
