# This file defines a function called fetch
cmake_minimum_required( VERSION 3.18 )

# Download F_URL and extract it
# If DATA is not empty then move the DATA file/directory out of it and into BASE_DIR (removes other files)
# If(PROGRESS); download progress will be provided
# If HASH is not "", verifies that the hash of the downloaded file matches
# HASH should be in the form of: "algo:hash"
# Note DATA may not end in: _extracted_download.tmp
function(fetch BASE_DIR F_URL DATA PROGRESS HASH)
    # Clean
    if (EXISTS "${BASE_DIR}")
        message(STATUS "Removing existing: ${BASE_DIR}")
        file(REMOVE_RECURSE "${BASE_DIR}")
    endif()
    make_directory("${BASE_DIR}")

    # Options
    if (PROGRESS)
        set(SHOW_PROGRESS "SHOW_PROGRESS")
    endif()
    if(NOT HASH STREQUAL "")
        set(HASH_CHECK "EXPECTED_HASH ${HASH}")
    endif()

    # Download
    message(STATUS "Downloading: ${F_URL}")
    set(COMPRESSED "${BASE_DIR}/raw_download")
    file(DOWNLOAD "${F_URL}" "${COMPRESSED}"
            TIMEOUT 600 # 10 minutes
            ${HASH_CHECK} # This should *not* be quoted
            TLS_VERIFY ON
            ${SHOW_PROGRESS} # This should *not* be quoted
            STATUS DOWNLOAD_STATUS
            )
    # Check if download was successful.
    list(GET DOWNLOAD_STATUS 0 STATUS_CODE)
    if(NOT STATUS_CODE EQUAL 0)
        list(GET DOWNLOAD_STATUS 1 ERROR_MESSAGE)
        message(FATAL_ERROR "Error occurred during Z3 download: ${ERROR_MESSAGE}")
    endif()

    # Extract and remove the compressed file
    message(STATUS "Extracting: ${COMPRESSED}")
    file(ARCHIVE_EXTRACT
            INPUT "${COMPRESSED}"
            DESTINATION "${BASE_DIR}"
            )
    file(REMOVE "${COMPRESSED}")

    # Get extracted directory name
    file(GLOB CHILDREN LIST_DIRECTORIES TRUE "${BASE_DIR}/*")
    list(LENGTH CHILDREN LEN)
    if(NOT LEN EQUAL 1)
        message(FATAL_ERROR
                "Failed to located extracted item within: ${BASE_DIR}"
                " There should only be one item in this directory!"
                )
    endif()
    list(GET CHILDREN 0 EXTRACTED_DIR)

    # Extract headers
    if (NOT DATA STREQUAL "")
        message(STATUS "Moving ${DATA} into: ${BASE_DIR}")
        set(TMP "${BASE_DIR}/_extracted_download.tmp")
        file(RENAME "${EXTRACTED_DIR}" "${TMP}")
        file(RENAME "${TMP}/boost" "${BASE_DIR}/boost")
        file(REMOVE_RECURSE "${TMP}")
    endif()
endfunction()
