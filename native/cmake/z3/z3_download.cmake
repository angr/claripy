# This file configures a make target for z3, which other targets can depend on
#
# The following variables should be defined before including this file:
#  Z3_DOWNLOAD_LINK - The link to download the z3 compressed file from
#                     The link must be the compressed z3 install directory containing 'bin' and 'include'
#  Z3_LIB           - The location of the z3 library once installed
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

	# Z3 download location
	set(DOWNLOAD_DIR "${Z3_DIR}/download/")
	set(COMPRESSED "${DOWNLOAD_DIR}/z3-compressed")

	# Setup download hash command
	if(DEFINED Z3_DOWNLOAD_HASH OR DEFINED Z3_DOWNLOAD_HASH_TYPE)
		if(NOT DEFINED Z3_DOWNLOAD_HASH OR NOT DEFINED Z3_DOWNLOAD_HASH_TYPE)
			message(FATAL_ERROR
				"Z3_DOWNLOAD_HASH and Z3_DOWNLOAD_HASH_TYPE should either both be defined"
				" or both be undefined; however, one cannot be defined without the other."
			)
		else()
			set(DOWNLOAD_ENABLE_HASH
				"EXPECTED_HASH"
				"${Z3_DOWNLOAD_HASH_TYPE}=${Z3_DOWNLOAD_HASH}"
			)
		endif()
	endif()

	# Show progress
	if(Z3_DOWNLOAD_SHOW_PROGRESS)
		set(PROGRESS "SHOW_PROGRESS")
	endif()

	# Download the compressed file
	message(STATUS "Downloading Z3 from: ${Z3_DOWNLOAD_LINK}")
	file(DOWNLOAD "${Z3_DOWNLOAD_LINK}" "${COMPRESSED}"
		TIMEOUT "${Z3_DOWNLOAD_TIMEOUT_SECONDS}"
		TLS_VERIFY "${Z3_DOWNLOAD_TLS_VERIFY}"
		${DOWNLOAD_ENABLE_HASH} # This should *not* be quoted
		${PROGRESS} # This should *not* be quoted
		STATUS DOWNLOAD_STATUS
	)
	# Check if download was successful.
	list(GET DOWNLOAD_STATUS 0 STATUS_CODE)
	if(NOT STATUS_CODE EQUAL 0)
		list(GET DOWNLOAD_STATUS 1 ERROR_MESSAGE)
		message(FATAL_ERROR "Error occurred during Z3 download: ${ERROR_MESSAGE}")
	endif()

	# Extract and remove the compressed file
	message(STATUS "Extracting Z3")
	file(ARCHIVE_EXTRACT
		INPUT "${COMPRESSED}"
		DESTINATION "${DOWNLOAD_DIR}"
	)
	file(REMOVE "${COMPRESSED}")

	# Get extracted directory name
	file(GLOB CHILDREN LIST_DIRECTORIES TRUE "${DOWNLOAD_DIR}/*")
	list(LENGTH CHILDREN LEN)
	if(NOT LEN EQUAL 1)
		message(FATAL_ERROR
			"Z3 download dirctory: ${DOWNLOAD_DIR} is polluted."
			" Refusing to continue. Please clean it and try again."
		)
	endif()
	list(GET CHILDREN 0 EXTRACTED_DIR)

	# Verification
	set(LIB_LOCATION "${EXTRACTED_DIR}/bin/${Z3_LIB_NAME}")
	if (NOT EXISTS "${LIB_LOCATION}")
		message(FATAL_ERROR
			"Downloaded files do not seem to contain: ${Z3_LIB_NAME}."
			" Perhaps this link is for a different operating system"
			" / the library has an unexpected file extension (a dll on linux, for example)."
		)
	endif()

	# Setup install tree and cleanup
	message(STATUS "Installing Z3 with build directory")
	file(MAKE_DIRECTORY "${Z3_DIR}/bin/")
	file(RENAME "${LIB_LOCATION}" "${Z3_LIB}")
	file(RENAME "${EXTRACTED_DIR}/include/" "${Z3_DIR}/include/")
	file(REMOVE_RECURSE "${EXTRACTED_DIR}")

endfunction()

_download_z3()
