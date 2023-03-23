#!/bin/bash -eux

# Args
NAME="${1}"
HEADERS="${2}"
shift 2

# Bindings
/usr/local/bin/binder \
	--config="./binder/clari.conf" \
	\
	-v \
	--single-file \
	--include-pybind11-stl \
	--root-module "${NAME}" \
	--prefix "/output" \
	"${HEADERS}" \
	-- \
	"$@" \
	-ffile-prefix-map="/native/"=/ \
	-Werror \
	-Wno-error=cpp \
	-std=c++17
