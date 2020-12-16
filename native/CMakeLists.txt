cmake_minimum_required(VERSION 3.16)

#################################################
#                                               #
#                  Set by user                  #
#                                               #
#################################################


option(BUILD_DOC "Build documentation" ON)
# TODO: automate cpplint, clang-format?

# Run make <DOC_MAKE_TARGET> to build documentation
set(DOC_MAKE_TARGET docs)

### Developer options below ###

# Version
set(VERSION 0.1) # TODO:

# Debug mode options. Comment out to disable
option(DEBUG_MODE "Enable debug mode" ON)

# For YouCompleteMe vim plugin
# Disable for non-developers
option(CMAKE_EXPORT_COMPILE_COMMANDS "Useful for development" ON)


#################################################
#                                               #
#               Program Constants               #
#                                               #
#################################################


# Define the project
set(PROJECT_NAME Claricpp)
project(${PROJECT_NAME} C CXX)


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
if(DEBUG_MODE)
    message("Debug Mode ON!")

    # Compile the program for debugging
    set(CMAKE_BUILD_TYPE debug)
    add_definitions(-DDEBUG_MODE)
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -O0 -g -ggdb -Wno-unused-parameter")

# Not debug mode
else()
    message("Debug Mode OFF!")
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -O3")
endif()


#################################################
#                                               #
#                    Doxygen                    #
#                                               #
#################################################


if(BUILD_DOC)

	# Find packages
	find_package(Doxygen REQUIRED dot)

	# Config
	set(PROJECT_LOGO "${CMAKE_CURRENT_SOURCE_DIR}/logo.png")
	set(DOXYGEN_IN "${CMAKE_CURRENT_SOURCE_DIR}/Doxyfile.in")
	set(DOXYGEN_OUT "${CMAKE_CURRENT_SOURCE_DIR}/Doxyfile")
	set(DOXYGEN_OUTPUT_DIRECTORY "/docs")

	# Copy DOXYGEN_IN -> DOXYGEN_OUT but replace all strings in DOXYGEN_IN
	# surrounded with @ signs with the values of the variables they name
	# For example: @PROJECT_LOGO@ is replaced with the value of PROJECT_LOGO
	configure_file("${DOXYGEN_IN}" "${DOXYGEN_OUT}" @ONLY)

	# Create a make target to generate documentation
	add_custom_target("${DOC_MAKE_TARGET}"
		COMMAND "${DOXYGEN_EXECUTABLE}" "${DOXYGEN_OUT}"
		WORKING_DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}"
		COMMENT "Generating documentation via Doxygen"
		VERBATIM
	)

endif(BUILD_DOC)

#################################################
#                                               #
#            Creating the support lib           #
#                                               #
#################################################


# src has its own cmake file
add_subdirectory(./src)
