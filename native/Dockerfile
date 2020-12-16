FROM ubuntu:20.04
SHELL [ "/bin/bash", "-c" ]

# Install dependencies for building, static analysis, and documentation
ENV DEBIAN_FRONTEND=noninteractive
RUN apt-get update
RUN apt-get install -yq \
	cppcheck \
	graphviz \
	doxygen \
	gnupg2 \
	cmake \
	make \
	wget \
	g++

# Install clang-format 11
RUN wget -O - 'https://apt.llvm.org/llvm-snapshot.gpg.key' | apt-key add -
RUN echo 'deb http://apt.llvm.org/focal/ llvm-toolchain-focal-11 main' >> /etc/apt/sources.list
RUN echo 'deb-src http://apt.llvm.org/focal/ llvm-toolchain-focal-11 main' >> /etc/apt/sources.list
RUN apt-get update
RUN apt-get install -yq \
	clang-format-11

# Copy in source files
ARG NATIVE='/native'
ARG SRC="${NATIVE}/src/"
COPY . "${NATIVE}"

# cpplint
RUN cppcheck "${SRC}"

# clang-format
WORKDIR "${NATIVE}"
RUN find . -regex '.*\.\(cpp\|hpp\)' -exec \
	clang-format-11 -style=file -i {} \;

# Config
ARG MAKE_TARGETS=all
ARG BUILD='/build'
RUN mkdir "${BUILD}"
WORKDIR "${BUILD}"
RUN cmake "${NATIVE}"

# Make
RUN make -j "$(nproc)" ${MAKE_TARGETS}
