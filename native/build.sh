#!/bin/bash -eux
set -o pipefail


# Optional env arguments for build.sh
DOCKER_TARGET="${DOCKER_TARGET:-test}"
PROGRESS="${PROGRESS:-tty}"

# Optional env arguments passed as --build-args to docker
CXX_COMPILER="${CXX_COMPILER:-g++}"
FORMAT="${FORMAT:-False}"
CMAKE_BUILD_TYPE="${CMAKE_BUILD_TYPE:-Debug}"
CMAKE_VERBOSE_MAKEFILE="${CMAKE_VERBOSE_MAKEFILE:-OFF}"
NUM_CORES="${NUM_CORES:-"$(nproc)"}"
VERBOSE_TEST="${VERBOSE_TEST:-False}"


# Get the version
VERSION="$(cat ../VERSION)"

# Use docker build kit by default (only builds dependent stages among other benefits)
if [[ -z "${DOCKER_BUILDKIT:-}" ]]; then
	export DOCKER_BUILDKIT=1
fi

# Build claricpp:<VERSION>
CTAG="${DOCKER_TARGET}-$(echo "${CXX_COMPILER}" | tr -cd '[:alnum:]')-${VERSION}"
docker build -t claricpp:"${CTAG}" \
	--target "${DOCKER_TARGET}" \
	--progress="${PROGRESS}" \
	`# Base ` \
	--build-arg CXX_COMPILER="${CXX_COMPILER}" \
	`# Config ` \
	--build-arg VERSION="${VERSION}" \
	--build-arg FORMAT="${FORMAT}" \
	`# CMake ` \
	--build-arg CMAKE_BUILD_TYPE="${CMAKE_BUILD_TYPE}" \
	--build-arg CMAKE_VERBOSE_MAKEFILE="${CMAKE_VERBOSE_MAKEFILE}" \
	`# Build ` \
	--build-arg NUM_CORES="${NUM_CORES}" \
	`# Test ` \
	--build-arg VERBOSE_TEST="${VERBOSE_TEST}" \
	.

# Tag the build as latest
docker tag claricpp:"${CTAG}" claricpp
