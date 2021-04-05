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


# Z3 download location
set(Z3_DOWNLOAD_DIR "${Z3_DIR}/download/")
set(Z3_COMPRESSED "${Z3_DOWNLOAD_DIR}/z3.zip")

# Reuse existing z3 install if possible
if(EXISTS "${Z3_LIB}")
	message(STATUS "Existing z3 library, prioritizing it over all else.")
else()

	# Setup download hash command
	if(DEFINED Z3_DOWNLOAD_HASH OR DEFINED Z3_DOWNLOAD_HASH_TYPE)
		if(NOT DEFINED Z3_DOWNLOAD_HASH OR NOT DEFINED Z3_DOWNLOAD_HASH_TYPE)
			message(FATAL_ERROR
				"Z3_DOWNLOAD_HASH and Z3_DOWNLOAD_HASH_TYPE should either both be defined"
				" or both be undefined; however, one cannot be defined without the other."
			)
		else()
			set(Z3_DOWNLOAD_ENABLE_HASH "${Z3_DOWNLOAD_HASH_TYPE}:${Z3_DOWNLOAD_HASH}")
		endif()
	endif()

	# Download the compressed file
	message(STATUS "Downloading Z3 from: ${Z3_DOWNLOAD_LINK}")
	file(DOWNLOAD "${Z3_DOWNLOAD_LINK}" "${Z3_COMPRESSED}"
		TIMEOUT "${Z3_DOWNLOAD_TIMEOUT_SECONDS}"
		${Z3_DOWNLOAD_HASH} # This should *not* be quoted
        STATUS Z3_DOWNLOAD_STATUS
		SHOW_PROGRESS
		TLS_VERIFY "${Z3_DOWNLOAD_TLS_VERIFY}"
	)
	# Check if download was successful.
	list(GET Z3_DOWNLOAD_STATUS 0 Z3_STATUS_CODE)
	if(NOT Z3_STATUS_CODE EQUAL 0)
		list(GET Z3_DOWNLOAD_STATUS 1 Z3_ERROR_MESSAGE)
		message(FATAL_ERROR "Error occurred during Z3 download: ${Z3_ERROR_MESSAGE}")
	endif()

	# Extract and remove the compressed file
	message(STATUS "Extracting Z3")
	file(ARCHIVE_EXTRACT
		INPUT "${Z3_COMPRESSED}"
		DESTINATION "${Z3_DOWNLOAD_DIR}"
	)
	file(REMOVE "${Z3_COMPRESSED}")

	# Get extracted directory name
	file(GLOB Z3_CHILDREN LIST_DIRECTORIES TRUE "${Z3_DOWNLOAD_DIR}/*")
	list(LENGTH Z3_CHILDREN Z3_LEN)
	if(NOT Z3_LEN EQUAL 1)
		message(FATAL_ERROR
			"Z3 download dirctory: ${Z3_DOWNLOAD_DIR} is polluted."
			" Refusing to continue. Please clean it and try again."
		)
	endif()
	list(GET Z3_CHILDREN 0 Z3_EXTRACTED_DIR)

	# Setup install tree and cleanup
	message(STATUS "Installing Z3 with build directory")
	file(MAKE_DIRECTORY "${Z3_DIR}/bin/")
	file(RENAME "${Z3_EXTRACTED_DIR}/bin/${Z3_LIB_NAME}" "${Z3_LIB}")
	file(RENAME "${Z3_EXTRACTED_DIR}/include/" "${Z3_DIR}/include/")
	file(REMOVE_RECURSE "${Z3_EXTRACTED_DIR}")

endif()
