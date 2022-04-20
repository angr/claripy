#!/bin/bash -eux

# Args
DEBUG_MODE="${1}"
Z3_HEADERS="${2}"
NATIVE="${3}"
OUTD="${4}"

# Bindings
API_D="${NATIVE}/api/"
/usr/local/bin/binder \
	--config="${API_D}/clari.conf"  \
	\
	-v \
	--root-module clari \
	--prefix "${OUTD}"  \
	"${API_D}/headers.hpp" \
	-- \
	-isystem "${Z3_HEADERS}" \
	-isystem "${NATIVE}/boost/" \
	-isystem "${NATIVE}/gmp/include/" \
	-isystem "${NATIVE}/backward-cpp" \
	\
	-DDEBUG="${DEBUG_MODE}" \
	-DDEBUGMODE="${DEBUG_MODE}" \
	\
	-ffile-prefix-map="${NATIVE}/"=/ \
	-Werror \
	-Wno-error=cpp \
	-std=c++17

