#!/bin/bash -eux
set -o pipefail


# Optional env arguments for build.sh
DOCKER_TARGET="${DOCKER_TARGET:-test}"

# Optional env arguments passed as --build-args to docker
CXX_COMPILER="${CXX_COMPILER:-g++}"
FORMAT="${FORMAT:-False}"
CMAKE_BUILD_TYPE="${CMAKE_BUILD_TYPE:-Debug}"
VERBOSE_TEST="${VERBOSE_TEST:-False}"


# Get the version
VERSION="$(cat ../VERSION)"

# Use docker build kit (only builds dependent stages among other benefits)
export DOCKER_BUILDKIT=1

# Build claricpp:<VERSION>
docker build --target "${DOCKER_TARGET}" -t claricpp:"${VERSION}" \
	`# Base ` \
	--build-arg CXX_COMPILER="${CXX_COMPILER}" \
	`# Config ` \
	--build-arg VERSION="${VERSION}" \
	--build-arg FORMAT="${FORMAT}" \
	`# CMake ` \
	--build-arg CMAKE_BUILD_TYPE="${CMAKE_BUILD_TYPE}" \
	`# Test ` \
	--build-arg VERBOSE_TEST="${VERBOSE_TEST}" \
	.

# Tag the build as latest
docker tag claricpp:"${VERSION}" claricpp
