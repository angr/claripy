##################################################
#                   Base Stage                   #
##################################################


FROM ubuntu:20.04 AS base
LABEL claricpp=base
SHELL [ "/bin/bash", "-ecux" ]

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
	cmake \
	make \
	g++
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

# Optional build args
ARG FORMAT="False"

# Build constants
ENV CLARIPY="/claripy/"
ENV NATIVE="${CLARIPY}/native/"
ENV SRC="${NATIVE}/src/"
ENV BUILD="/build/"

# Require Version argument
RUN if [[ -z "${VERSION}" ]]; then \
		echo "Error: VERSION is a required build argument!" \
		exit 1; \
	fi

# Copy in source files
COPY . "${NATIVE}"
RUN echo "${VERSION}" > "${CLARIPY}/VERSION"

# Optional clang-format
WORKDIR "${NATIVE}"
RUN if [[ "${FORMAT}" == True ]]; then \
		find . -regex '.*\.\(cpp\|hpp\|\)' -exec \
			clang-format-11 -style=file -i {} ';' ; \
	fi


##################################################
#                  CMake Stage                   #
##################################################


FROM config as cmake
LABEL claricpp=cmake

# Optional build args
ARG CMAKE_BUILD_TYPE="Debug"

# cd build
RUN mkdir "${BUILD}"
WORKDIR "${BUILD}"

# CMake
RUN cmake -DCMAKE_BUILD_TYPE="${CMAKE_BUILD_TYPE}" "${NATIVE}"


##################################################
#                  Build Stage                   #
##################################################


FROM cmake as build
LABEL claricpp=build

# Make
RUN make -j "$(nproc)" claricpp


##################################################
#                Test Build Stage                #
##################################################


FROM build as test_build
LABEL claricpp=test_build

# Build the test cases
RUN make -j "$(nproc)" all


##################################################
#                   Test Stage                   #
##################################################


FROM test_build as test
LABEL claricpp=test

# Optional build args
ARG VERBOSE_TEST="False"

# Test if make targets request it
RUN if [[ "${VERBOSE_TEST}" == True ]]; then \
		ctest --verbose -j "$(nproc)" . ; \
	else \
		ctest -j "$(nproc)" . ; \
	fi


##################################################
#                   Docs Stage                   #
##################################################


FROM test_build as docs
LABEL claricpp=docs

# Make docs
RUN make docs
