#!/bin/bash -eu

# Config
NAME="clari"
DEBUG_MODE=0

# Sanity check
if [[ "${VIRTUAL_ENV:-}" == "" && "${FORCE_GEN:-}" != 1 ]]; then
	echo "Run from the venv with z3 installed"
	echo "Set FORCE_GEN=1 to override this."
	exit 1
fi

# Python packages
Z3="$(python3 -c "import z3, os; print(os.path.dirname(z3.__file__))")/include"
PY="$(python3 -c 'from distutils.sysconfig import get_python_inc as f; print(f())')"

# Dirs
BINDER_D="$( cd "$(dirname "${BASH_SOURCE[0]}")" >/dev/null 2>&1 && pwd )"
API_D="$(realpath "${BINDER_D}/../")"
AUTOGEN="${API_D}/autogen.cpp"
NATIVE="$(realpath "${API_D}/../../")"
OUTPUT="${BINDER_D}/raw"

# Prep
echo "Removing old bindings"
rm -rf "${OUTPUT}" || true
mkdir "${OUTPUT}"

# Gen
echo "Creating new bindings"
INCLUDES=(
	-isystem "${PY}"
	-isystem "${Z3}"
	-isystem "/native/pybind11/include"
	-isystem "/native/boost/"
	-isystem "/native/gmp/include"
	-isystem "/native/backward-cpp"
)
set -x
docker run --rm \
	--user "$(id -u):$(id -g)" \
	`# Mount in everything` \
	-v "${Z3}:${Z3}:ro" \
	-v "${PY}:/${PY}:ro" \
	-v "${NATIVE}:/native:ro" \
	-v "${BINDER_D}:/binder:ro" \
	-v "${OUTPUT}:/output" \
	`# Run binder` \
	-it zwimer/binder:15 \
	"/binder/cmd.sh" \
		"${NAME}" \
		"/native/src/api/headers.hpp" \
		-DDEBUG="${DEBUG_MODE}" \
		-DDEBUGMODE="${DEBUG_MODE}" \
		"${INCLUDES[@]}"
set +x
echo "Bindings generated"

# Permissions
if [[ "$(uname -s)" == "Darwin" ]]; then
	echo "Mac detected: Removing ACLs of output directory"
	chmod -N "${OUTPUT}"
fi

# Autogen
echo "Removing outdated ${AUTOGEN}"
rm "${AUTOGEN}" || true
echo "Recreating autogen.cpp"
set -x
python3 format.py \
	"${OUTPUT}" \
	"${AUTOGEN}" \
	"${NAME}" \
	"API::Binder" \
	`# Includes` \
	"manual.hpp" \
	"headers.hpp"
