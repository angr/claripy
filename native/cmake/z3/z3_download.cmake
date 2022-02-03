# This file configures a make target for z3, which other targets can depend on
#
# The following variables should be defined before including this file:
#  Z3_DOWNLOAD_LINK - The link to download the z3 compressed file from
#                     The link must be the compressed z3 install directory containing 'bin' and 'include'
#  Z3_LIB           - The location of the z3 library once installed
#  Z3_DIR           - The directory containing all made / downloaded z3 artifacts
#  Z3_LIB_NAME      - The name of the z3 library
#  Z3_DOWNLOAD_TLS_VERIFY      - Specify whether to verify the server certificate for https:// urls
#  Z3_DOWNLOAD_TIMEOUT_SECONDS - The download timeout in seconds
#  Z3_DOWNLOAD_HASH      (Optional) - Specifies the hash of the download file if hash checking is desired
#                                     Must be defiend with Z3_DOWNLAD_HASH_TYPE
#  Z3_DOWNLOAD_HASH_TYPE (Optional) - Specifies the type of the hash Z3_DOWNLOAD_HASH is
#                                     Must be defiend with Z3_DOWNLAD_HASH

# We rely on 3.18 features here
cmake_minimum_required( VERSION 3.18 )

# Wrapping this in a function to create a new scope
function(_download_z3)

	# Setup download hash command
	if(DEFINED Z3_DOWNLOAD_HASH OR DEFINED Z3_DOWNLOAD_HASH_TYPE)
		if(NOT DEFINED Z3_DOWNLOAD_HASH OR NOT DEFINED Z3_DOWNLOAD_HASH_TYPE)
			message(FATAL_ERROR
				"Z3_DOWNLOAD_HASH and Z3_DOWNLOAD_HASH_TYPE should either both be defined"
				" or both be undefined; however, one cannot be defined without the other."
			)
		else()
			set(HASH "${Z3_DOWNLOAD_HASH_TYPE}=${Z3_DOWNLOAD_HASH}")
		endif()
	endif()

	fetch("${Z3_DIR}/download" "${Z3_DOWNLOAD_LINK}" "" "${Z3_DOWNLOAD_SHOW_PROGRESS}" "${HASH}")

	# Setup install tree and cleanup
	message(STATUS "Installing Z3 with build directory")
	get_filename_component(D "${Z3_LIB}" DIRECTORY)
	file(MAKE_DIRECTORY "${D}")
	file(RENAME "${EXTRACTED_DIR}/bin/${Z3_LIB_NAME}" "${Z3_LIB}")
	file(RENAME "${EXTRACTED_DIR}/include/" "${Z3_INCLUDE_DIR}")
	file(REMOVE_RECURSE "${EXTRACTED_DIR}")

endfunction()

_download_z3()
