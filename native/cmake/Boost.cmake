# This file acquires Boost
# Relevant input variables:
#   - BOOST_URL: A URL to download boost from; if empty find_package will be used
#   - BOOST_HASH_CHECK: A optional hash algorithm and hash the download should have; ignored if empty or BOOST_URL is empty
#   - BOOST_DIR: The directory to create and store boost in; ignored if BOOST_URL is empty
#   - BOOST_FORCE_CLEAN_DOWNLOAD: Force a clean download of boost; ignored if BOOST_URL is empty

# We rely on 3.18 features here
cmake_minimum_required( VERSION 3.18 )

function(_download_boost)
    # Clean
    if (EXISTS "${BOOST_DIR}")
        message(STATUS "Cleaning: ${BOOST_DIR}")
        file(REMOVE_RECURSE "${BOOST_DIR}")
    endif()
    make_directory("${BOOST_DIR}")

    # Download
    message(STATUS "Downloading Boost from: ${BOOST_URL}")
    set(COMPRESSED "${BOOST_DIR}/raw_download")
    file(DOWNLOAD "${BOOST_URL}" "${COMPRESSED}"
            TIMEOUT 600 # 10 minutes
            ${HASH_CHECK} # This should *not* be quoted
            TLS_VERIFY ON
            # SHOW_PROGRESS
            STATUS DOWNLOAD_STATUS
            )
    # Check if download was successful.
    list(GET DOWNLOAD_STATUS 0 STATUS_CODE)
    if(NOT STATUS_CODE EQUAL 0)
        list(GET DOWNLOAD_STATUS 1 ERROR_MESSAGE)
        message(FATAL_ERROR "Error occurred during Z3 download: ${ERROR_MESSAGE}")
    endif()

    # Extract and remove the compressed file
    message(STATUS "Extracting Boost from: ${COMPRESSED}")
    file(ARCHIVE_EXTRACT
            INPUT "${COMPRESSED}"
            DESTINATION "${BOOST_DIR}"
            )
    file(REMOVE "${COMPRESSED}")

    # Get extracted directory name
    file(GLOB CHILDREN LIST_DIRECTORIES TRUE "${BOOST_DIR}/*")
    list(LENGTH CHILDREN LEN)
    if(NOT LEN EQUAL 1)
        message(FATAL_ERROR
                "Failed to located extracted boost directory within: ${BOOST_DIR}"
                " There should only be one item in this directory!"
                )
    endif()
    list(GET CHILDREN 0 EXTRACTED_DIR)

    # Extract headers
    message(STATUS "Installing boost headers into: ${BOOST_DIR}")
    set(TMP "${BOOST_DIR}/downloaded")
    file(RENAME "${EXTRACTED_DIR}" "${TMP}")
    file(RENAME "${TMP}/boost" "${BOOST_DIR}/boost")
    file(REMOVE_RECURSE "${TMP}")
endfunction()


if (BOOST_URL STREQUAL "")
    find_package(Boost 1.7 REQUIRED)
elseif (BOOST_FORCE_CLEAN_DOWNLOAD OR NOT EXISTS "${BOOST_DIR}")
    _download_boost()
    message(STATUS "Setting Boost_INCLUDE_DIRS to: ${BOOST_DIR}")
    set(Boost_INCLUDE_DIRS "${BOOST_DIR}")
endif()