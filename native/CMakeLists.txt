cmake_minimum_required(VERSION 3.5)

#################################################
#                                               #
#                  Set by user                  #
#                                               #
#################################################


### Developer options below ###


# Debug mode options. Comment out to disable
# set(DEBUG_MODE "VERBOSE")
set(DEBUG_MODE "ON")

# For YouCompleteMe vim plugin
# Disable for non-developers
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)


#################################################
#                                               #
#               Program Constants               #
#                                               #
#################################################


# Set the program name
set(PROGRAM_NAME Claricpp)
project(${PROGRAM_NAME} C CXX)


#################################################
#                                               #
#              Automated - General              #
#                                               #
#################################################


# Require C++ 17
set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

# Required complication flags
set (CMAKE_CXX_FLAGS "-std=c++17 -Wall -Wextra -Werror" )

# If debug mode
if(DEFINED DEBUG_MODE)
    message("Debug Mode ON!")

    # If verbose
    if(DEBUG_MODE STREQUAL "VERBOSE")
        message("\t Verbose Debug Mode ON!")
        add_definitions(-DVERBOSE)
    endif()

    # Compile the program for debugging
    set(CMAKE_BUILD_TYPE debug)
    add_definitions(-DDEBUG_MODE)
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -O0 -ggdb -Wno-unused-parameter")

# Not debug mode
else()
    message("Debug Mode OFF!")
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -O2")
endif()


#################################################
#                                               #
#            Creating the support lib           #
#                                               #
#################################################


# Create the .so
add_library(${SS_SUPPORT_LIB} SHARED
    src/ops/operations.cpp
    )
