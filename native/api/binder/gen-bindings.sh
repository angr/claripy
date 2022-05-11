#!/bin/bash -eux
MY_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
NATIVE="$(realpath "${MY_DIR}/../../../native")" # ../native just in case

# Checks
which realpath > /dev/null
which python3 > /dev/null

# Config
API_D="${NATIVE}/api"
CMD_SH="${MY_DIR}/docker_cmd.sh"
OUTPUT="${API_D}/binder/raw_output"
Z3_HEADERS="$(python3 -c 'import z3, os; print(os.path.dirname(z3.__file__))')/include"
AUTOGEN="${API_D}/autogen.cpp"

# Prep
echo "Removing old bindings"
rm -rf "${OUTPUT}" || true
mkdir "${OUTPUT}"

# Gen
echo "Creating new bindings"
DOCKER_CMD_SH="/cmd.sh"
DOCKER_Z3_HEADERS="/z3-headers"
docker run --rm \
	--user "$(id -u):$(id -g)" \
	`# Mount in everything` \
	-v "${CMD_SH}:${DOCKER_CMD_SH}:ro" \
	-v "${Z3_HEADERS}:/${DOCKER_Z3_HEADERS}:ro" \
	-v "${NATIVE}:${NATIVE}:ro" \
	-v "${OUTPUT}:${OUTPUT}" \
 	-it "zwimer/binder:14" \
	`# Run binder` \
	"${DOCKER_CMD_SH}" \
	0 "${DOCKER_Z3_HEADERS}" "${NATIVE}" "${OUTPUT}"
echo "Bindings generated"

# Permissions
if [[ "$(uname -s)" == "Darwin" ]]; then
	echo "Mac detected: Removing ACLs of output directory"
	chmod -N "${OUTPUT}"
fi

# Rm old autogen
echo "Removing outdated ${AUTOGEN}"
rm "${AUTOGEN}" || true
echo "Run cmake to recreate autogen.cpp"
