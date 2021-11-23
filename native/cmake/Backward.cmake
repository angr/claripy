# This file configures Backward
#
# This file defines the following functions:
#  add_backward - This function can be called on a target and will include headers / links as needed to use backward

function(_config_backward)
    message(STATUS "Configuring Backward")
    set(BW_DIR "${CMAKE_SOURCE_DIR}/backward-cpp/")

    # Error checking
    if (NOT EXISTS "${BW_DIR}")
        message( FATAL_ERROR "${BW_DIR} does not exist, maybe use 'git submodule update --init'?")
    endif()
    if (NOT IS_DIRECTORY "${BW_DIR}")
        message( FATAL_ERROR "${BW_DIR} is not a directory; maybe delete it then use 'git submodule update --init'?")
    endif()

    # Config
    set(BACKWARD_SHARED FALSE)
    set(BACKWARD_TESTS FALSE)
    add_subdirectory("${BW_DIR}")

    # Info
    if (LIBDW_FOUND OR LIBBFD_FOUND OR LIBDWARF_FOUND)
        message("Backward backend library found!")
    else()
        message(WARNING "Backward backend not library found; backtraces will be limited.")
    endif()
endfunction()

_config_backward()