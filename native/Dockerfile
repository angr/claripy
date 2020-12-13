FROM ubuntu:20.04
SHELL [ "/bin/bash", "-c" ]

# Install dependencies
ENV DEBIAN_FRONTEND=noninteractive
RUN apt-get update
RUN apt-get install -yq \
	clang-format \
	cppcheck \
	graphviz \
	doxygen \
	clang \
	cmake \
	make \
	g++

# Copy in source files
ARG NATIVE='/native'
ARG SRC="${NATIVE}/src/"
COPY . "${NATIVE}"

# cpplint
RUN cppcheck "${SRC}"

# clang-format
WORKDIR "${NATIVE}"
RUN find . -name '*.cpp' -or -name '*.hpp' -exec \
	clang-format -style=file -i {} \;

# Build
ARG BUILD='/build'
RUN mkdir "${BUILD}"
WORKDIR "${BUILD}"
RUN cmake -Duse_libclang=ON "${NATIVE}"
RUN make -j "$(nproc)"

# Build documentation
RUN make -j "$(nproc)" docs
