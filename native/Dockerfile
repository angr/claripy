FROM ubuntu:20.04
SHELL [ "/bin/bash", "-c" ]

# Install dependencies
ENV DEBIAN_FRONTEND=noninteractive
RUN apt-get update
RUN apt-get install -yq \
	software-properties-common \
	cppcheck \
	graphviz \
	doxygen \
	cmake \
	make \
	wget \
	g++

# Install clang-format-11
RUN wget -O - 'https://apt.llvm.org/llvm-snapshot.gpg.key' | apt-key add -
RUN apt-add-repository "deb http://apt.llvm.org/focal/ llvm-toolchain-focal-11 main"
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

# Build
ARG BUILD='/build'
RUN mkdir "${BUILD}"
WORKDIR "${BUILD}"
RUN cmake -Duse_libclang=ON "${NATIVE}"
RUN make -j "$(nproc)"

# Build documentation
RUN make -j "$(nproc)" docs
