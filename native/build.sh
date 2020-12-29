#!/bin/bash -eu

# Optional env arguments
FORMAT="${FORMAT:-False}"
CMAKE_BUILD_TYPE="${CMAKE_BUILD_TYPE:-Debug}"
MAKE_TARGETS="${MAKE_TARGETS:-}"
TEST="${TEST:-False}"
VERBOSE="${VERBOSE:-False}"
DOCKER_TARGET="${DOCKER_TARGET:-test}"


# Build the base
# No build context required
docker build -t claricpp:base - < base.docker

# Get the version
VERSION="$(cat ../VERSION)"

# Build claricpp:<VERSION>
docker build --target "${DOCKER_TARGET}" -t claricpp:"${VERSION}" \
	--build-arg VERSION="${VERSION}" \
	--build-arg FORMAT="False" \
	--build-arg CMAKE_BUILD_TYPE="Debug" \
	--build-arg MAKE_TARGETS="" \
	--build-arg VERBOSE="False" \
	.

# Tag the build as latest
docker tag claricpp:"${VERSION}" claricpp
