cmake_minimum_required(VERSION 3.16)

#################################################
#                                               #
#                  Set by user                  #
#                                               #
#################################################


# Config options
option(BUILD_DOC "Create a make target for documentation" ON)
option(ENABLE_TESTING "Create a make target for test cases" ON)
option(OPTIMIZE_FOR_NATIVE "Build with -march=native etc" ON)

# Static Analysis Options
option(CPP_CHECK "Enable cppcheck" ON)
option(IWYU "Enable iwyu" OFF)
option(LWYU "Enable lwyu" ON)
option(CLANG_TIDY "Enable clang-tidy" ON)

# Run make <DOC_MAKE_TARGET> to build documentation if BUILD_DOC is ON
set(DOC_MAKE_TARGET docs)

# Shared library name
set(SHARED_LIB_NAME claricpp.so)

### Developer options below ###

# Config options
option(ENABLE_MEMCHECK "Enable memcheck on test target" ON)
option(CMAKE_EXPORT_COMPILE_COMMANDS "Useful for development" ON)

# Version
set(VERSION 0.1)

# API Version
set(SOVERSION 1)

# Default build type
# Default to debug mode
# Can override this by running cmake with "-DCMAKE_BUILD_TYPE=Release"
if( NOT CMAKE_BUILD_TYPE )
	set( CMAKE_BUILD_TYPE Debug )
endif()


#################################################
#                                               #
#               Program Constants               #
#                                               #
#################################################


# Define the project
set(PROJECT_NAME Claricpp)
project("${PROJECT_NAME}" C CXX)


#################################################
#                                               #
#              Automated - General              #
#                                               #
#################################################


# Define standards
set(CMAKE_C_STANDARD 11)
set(CMAKE_CXX_STANDARD 17)
set(CMAKE_C_EXTENSIONS ON)
set(CMAKE_CXX_EXTENSIONS ON)
set(CMAKE_C_STANDARD_REQUIRED ON)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

# Required complication flags
set (CMAKE_C_FLAGS   "-Wall -Wextra -Werror" )
set (CMAKE_CXX_FLAGS "-Wall -Wextra -Werror" )

# Optimize for native code
if(OPTIMIZE_FOR_NATIVE)
	set (CMAKE_C_FLAGS   "${CMAKE_C_FLAGS}   -march=native -mtune=native" )
	set (CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -march=native -mtune=native" )
endif()

# Static Analysis
if(CPP_CHECK)
	set(CMAKE_C_CPPCHECK "cppcheck")
	set(CMAKE_CXX_CPPCHECK "cppcheck")
endif()
if(IWYU)
	if(APPLE)
		set(IWYU_PATH "include-what-you-use")
	else()
		set(IWYU_PATH "iwyu")
	endif()
	set(CMAKE_C_INCLUDE_WHAT_YOU_USE "${IWYU_PATH}")
	set(CMAKE_CXX_INCLUDE_WHAT_YOU_USE "${IWYU_PATH}")
endif()
if(LWYU)
	if(APPLE)
		message(WARNING "Link what you use is not supported by Apple's linker. Skipping.")
	else()
		set(CMAKE_LINK_WHAT_YOU_USE TRUE)
	endif()
endif()
if(CLANG_TIDY)
	# TODO: enable other checks as desired
	set(CMAKE_C_CLANG_TIDY clang-tidy -checks=*,readability=*,boost=*,clang-analyzer=*)
endif()

# Build type
if(CMAKE_BUILD_TYPE MATCHES DEBUG)
    add_definitions(-DDEBUG)
    message("Debug Mode ON!")
    set(CMAKE_C_FLAGS   "${CMAKE_C_FLAGS}   -O0 -g -fsanitize=all")
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -O0 -g -fsanitize=all")
elseif(CMAKE_BUILD_TYPE MATCHES RELEASE)
    message("Release Build ON!")
    set(CMAKE_C_FLAGS   "${CMAKE_C_FLAGS}   -O3")
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
#          Generate library and tests           #
#                                               #
#################################################


# Create a make target for the library
add_subdirectory(./src)

# Create a make target for test cases
if(ENABLE_TESTING)
	include(CTest)
	enable_testing()
	add_subdirectory(./tests)
endif()
