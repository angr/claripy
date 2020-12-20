FROM ubuntu:20.04
SHELL [ "/bin/bash", "-c" ]

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

# Install dependencies
# Build
RUN apt-get install -yq \
	cmake \
	make \
	g++
# Static Analysis
RUN apt-get install -yq \
	clang-format-11 \
	clang-tidy-11 \
	cppcheck \
	iwyu
# Documentation
RUN apt-get install -yq \
	graphviz \
	doxygen

# Copy in source files
ARG NATIVE='/native'
ARG SRC="${NATIVE}/src/"
COPY . "${NATIVE}"

# clang-format
WORKDIR "${NATIVE}"
RUN find . -regex '.*\.\(cpp\|hpp\)' -exec \
	clang-format-11 -style=file -i {} \;

# CMake
ARG MAKE_TARGETS=all
ARG BUILD='/build'
RUN mkdir "${BUILD}"
WORKDIR "${BUILD}"
RUN cmake "${NATIVE}"

# Make
RUN make -j "$(nproc)" ${MAKE_TARGETS}
