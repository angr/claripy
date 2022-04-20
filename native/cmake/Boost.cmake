# This file acquires Boost
# Relevant input variables:
#   - BOOST_URL: A URL to download boost from; if empty find_package will be used
#   - BOOST_HASH_CHECK: A optional hash algorithm and hash the download should have; ignored if empty or BOOST_URL is empty
#   - BOOST_DIR: The directory to create and store boost in; ignored if BOOST_URL is empty
#   - BOOST_FORCE_CLEAN_DOWNLOAD: Force a clean download of boost; ignored if BOOST_URL is empty

include(fetch)

if ((NOT Boost_INCLUDE_DIRS STREQUAL "") AND (NOT BOOST_URL STREQUAL ""))
    message(FATAL_ERROR "Boost_INCLUDE_DIRS and BOOST_URL both are non-empty; these two options conflict.")
endif()

if (Boost_INCLUDE_DIRS STREQUAL "")
    if (BOOST_URL STREQUAL "")
        find_package(Boost 1.7 REQUIRED)
    elseif (BOOST_FORCE_CLEAN_DOWNLOAD OR NOT EXISTS "${BOOST_DIR}")
        message("Getting boost...")
        fetch("${BOOST_DIR}" "${BOOST_URL}" "boost" OFF "${BOOST_HASH}")
        message(STATUS "Setting Boost_INCLUDE_DIRS to: ${BOOST_DIR}")
        set(Boost_INCLUDE_DIRS "${BOOST_DIR}")
    endif()
endif()