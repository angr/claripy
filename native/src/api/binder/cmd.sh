#!/bin/bash -eux

# Args
DEBUG_MODE="${1}"
HEADERS="${2}"
shift 2

# Bindings
/usr/local/bin/binder \
	--config="./binder/clari.conf" \
	\
	--stl \
	-v \
	--root-module clari \
	--prefix "/output" \
	"${HEADERS}" \
	-- \
	"$@" \
	\
	-DDEBUG="${DEBUG_MODE}" \
	-DDEBUGMODE="${DEBUG_MODE}" \
	\
	-ffile-prefix-map="/native/"=/ \
	-Werror \
	-Wno-error=cpp \
	-std=c++17
