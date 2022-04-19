#!/bin/bash -eux
MY_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"

# Checks
which realpath > /dev/null
which python3 > /dev/null

# Config
NATIVE="$(realpath "${MY_DIR}/..")"
CMD_SH="${MY_DIR}/docker_cmd.sh"
BINDER="${NATIVE}/src/api/binder"
Z3_HEADERS="$(python3 -c 'import z3, os; print(os.path.dirname(z3.__file__))')/include"
AUTOGEN="${NATIVE}/src/api/autogen.cpp"

# Prep
echo "Removing old bindings"
rm -rf "${BINDER}" || true
mkdir "${BINDER}"

# Gen
echo "Creating new bindings"
DOCKER_CMD_SH="/cmd.sh"
DOCKER_Z3_HEADERS="/z3-headers"
docker run --rm \
	`# Mount in everything` \
	-v "${CMD_SH}:${DOCKER_CMD_SH}:ro" \
	-v "${Z3_HEADERS}:/${DOCKER_Z3_HEADERS}:ro" \
	-v "${NATIVE}:${NATIVE}:ro" \
	-v "${BINDER}:${BINDER}" \
 	-it "zwimer/binder:14" \
	`# Run binder` \
	"${DOCKER_CMD_SH}" \
	0 "${DOCKER_Z3_HEADERS}" "${NATIVE}" "${BINDER}"
echo "Bindings generated"

# Rm old autogen
echo "Removing old autogen.cpp"
rm "${AUTOGEN}" || true
echo "Run cmake to recreate autogen.cpp"
