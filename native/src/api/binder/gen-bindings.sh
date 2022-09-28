#!/bin/bash -eux

# Config
Z3="$(python3 -c "import z3, os; print(os.path.dirname(z3.__file__))")/include"
PY="$(python3 -c 'from distutils.sysconfig import get_python_inc as f; print(f())')"

# Dirs
BINDER_D="$( cd "$(dirname "${BASH_SOURCE[0]}")" >/dev/null 2>&1 && pwd )"
API_D="$(realpath "${BINDER_D}/../")"
NATIVE="$(realpath "${API_D}/../../")"
OUTPUT="${BINDER_D}/raw_output"
AUTOGEN="${BINDER_D}/autogen.cpp"

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
docker run --rm \
	--user "$(id -u):$(id -g)" \
	`# Mount in everything` \
	-v "${Z3}:${Z3}:ro" \
	-v "${PY}:/${PY}:ro" \
	-v "${NATIVE}:/native:ro" \
	-v "${BINDER_D}:/binder:ro" \
	-v "${OUTPUT}:/output" \
	`# Run binder` \
	-it zwimer/binder:14 \
	"/binder/cmd.sh" 0 "/native/src/api/headers.hpp" "${INCLUDES[@]}"
echo "Bindings generated"

# Permissions
if [["$(uname -s)" == "Darwin"]]; then
	echo "Mac detected: Removing ACLs of output directory"
	chmod -N "${OUTPUT}"
fi

# Rm old autogen
echo "Removing outdated ${AUTOGEN}"
rm "${AUTOGEN}" || true
echo "Run cmake to recreate autogen.cpp"
