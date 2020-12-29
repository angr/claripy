#!/bin/bash -eux
set -o pipefail


# Optional env arguments for build.sh
DOCKER_TARGET="${DOCKER_TARGET:-test}"

# Optional env arguments passed as --build-args to docker
FORMAT="${FORMAT:-False}"
CMAKE_BUILD_TYPE="${CMAKE_BUILD_TYPE:-Debug}"
MAKE_TARGET="${MAKE_TARGET:-claricpp}"
VERBOSE_TEST="${VERBOSE_TEST:-False}"


# Get the version
VERSION="$(cat ../VERSION)"


# Build claricpp:<VERSION>
docker build --target "${DOCKER_TARGET}" -t claricpp:"${VERSION}" \
	`# Config ` \
	--build-arg VERSION="${VERSION}" \
	--build-arg FORMAT="${FORMAT}" \
	`# CMake ` \
	--build-arg CMAKE_BUILD_TYPE="${CMAKE_BUILD_TYPE}" \
	`# Make ` \
	--build-arg MAKE_TARGET="${MAKE_TARGET}" \
	`# Test ` \
	--build-arg VERBOSE_TEST="${VERBOSE_TEST}" \
	.

# Tag the build as latest
docker tag claricpp:"${VERSION}" claricpp
