cmake_minimum_required( VERSION 3.16 )

#################################################
#                                               #
#                  Set by user                  #
#                                               #
#################################################


# Shared library name
set( SHARED_LIB_NAME "claricpp.so" )

# Config options
option( BUILD_DOC "Create a make target for documentation"   ON )
option( ENABLE_TESTING "Create a make target for test cases" ON )
option( OPTIMIZE_FOR_NATIVE "Build with -march=native etc"   ON )

### Developer options below ###

# Version / API Version
set( VERSION 0.1 )
set( SOVERSION 1 )

# Run make <DOC_MAKE_TARGET> to build documentation if BUILD_DOC is ON
set( DOC_MAKE_TARGET docs )

# Static Analysis Options
option( IWYU "Enable iwyu" OFF )
option( LWYU "Enable lwyu" ON )
option( CPP_CHECK "Enable cppcheck" ON )
option( CLANG_TIDY "Enable clang-tidy" ON )

# Default build type
# Default to debug mode
# Can override this by running cmake with "-DCMAKE_BUILD_TYPE=Release"
set( CMAKE_BUILD_TYPE "Debug" CACHE STRING "Cmake build type" )

# Config options
# The memcheck and security options are mutually exclusive
# Note that ENABLE_SECURITY overrides the flags of every other option
option( ENABLE_MEMCHECK "Enable memcheck on test target" ON )
option( ALLOW_NO_MEMCHECK_APPLE "Allow not using memcheck on apple" ON )
option( ENABLE_SECURITY "Build security flags at the cost of runtime performance" OFF )
option( CMAKE_EXPORT_COMPILE_COMMANDS "Exports a json useful to IDEs and other tools" ON )
# If enabled: log calls to log levels lower than defined will have no performance penalty
option( CONSTANT_LOG_LEVEL "Force log level to be set at compiletime for release builds" OFF )

# Log levels are defined in ./src/utils/log/level/level/hpp
# Note: Lower log levels implier higher levels (i.e. verbose implies critical)
set( DEFAULT_RELEASE_LOG_LEVEL "Warning" )
set( DEFAULT_DEBUG_LOG_LEVEL "Debug" )
set( DEFAULT_LOG_LEVEL "Info" )


#################################################
#                                               #
#               Program Constants               #
#                                               #
#################################################


# Define the project
set(PROJECT_NAME Claricpp)
project("${PROJECT_NAME}" C CXX)

# Define standards
set(CMAKE_C_STANDARD 11)
set(CMAKE_CXX_STANDARD 17)
set(CMAKE_C_EXTENSIONS ON)
set(CMAKE_CXX_EXTENSIONS OFF)
set(CMAKE_C_STANDARD_REQUIRED ON)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

# Required complication flags
set (CMAKE_C_FLAGS   "-Wall -Wextra -Wpedantic -Werror" )
set (CMAKE_CXX_FLAGS "-Wall -Wextra -Werror" )

# Library source
# Used for compilation and header lookup for tests
set(LIBRARY_SRC "${CMAKE_CURRENT_SOURCE_DIR}/src")


#################################################
#                                               #
#                Static Analysis                #
#                                               #
#################################################


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
	set(CMAKE_C_CLANG_TIDY "clang-tidy" "-checks=*,readability=*,boost=*,clang-analyzer=*")
endif()


#################################################
#                                               #
#              Automated - General              #
#                                               #
#################################################


# Option verification
if(ENABLE_MEMCHECK AND APPLE AND NOT ALLOW_NO_MEMCHECK_APPLE)
	message(FATAL_ERROR "Memcheck is not compatible with the lastest versions of MacOS")
endif()

# Optimize for native code
if(OPTIMIZE_FOR_NATIVE)
	set(NATIVE_FLAGS "-march=native -mtune=native")
	set(CMAKE_C_FLAGS   "${CMAKE_C_FLAGS}   ${NATIVE_FLAGS}")
	set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${NATIVE_FLAGS}")
endif()

# Build type
if(CMAKE_BUILD_TYPE MATCHES Debug)
    message("*** Debug Mode enabled! ***")
	add_definitions(-DDEFAULT_LOG_LEVEL=${DEFAULT_DEBUG_LOG_LEVEL}) # no quotes because it is a C-macro
	# Add debug macro
    add_definitions(-DDEBUG)
	# Debug flags
	set(DEBUG_FLAGS
		"-O0"
		"-g"
		"-fasynchronous-unwind-tables"
		"-grecord-gcc-switches"
		"-D_GLIBCXX_ASSERTIONS"
	)
	string(REPLACE ";" " " DEBUG_FLAGS "${DEBUG_FLAGS}")
	set(CMAKE_CXX_FLAGS_DEBUG "${CMAKE_CXX_FLAGS_DEBUG} ${DEBUG_FLAGS}")
	set(CMAKE_C_FLAGS_DEBUG   "${CMAKE_C_FLAGS_DEBUG}   ${DEBUG_FLAGS}")
elseif(CMAKE_BUILD_TYPE MATCHES Release)
    message("*** Release Build enabled! ***")
	add_definitions(-DDEFAULT_LOG_LEVEL=${DEFAULT_RELEASE_LOG_LEVEL}) # no quotes because it is a C-macro
	# Release flags
	set(RELEASE_FLAGS "-pipe -flto -O3")
	set(CMAKE_CXX_FLAGS_RELEASE "${CMAKE_CXX_FLAGS_RELEASE} ${RELEASE_FLAGS}")
	set(CMAKE_C_FLAGS_RELEASE   "${CMAKE_C_FLAGS_RELEASE}   ${RELEASE_FLAGS}")
	set(CMAKE_SHARED_LINKER_FLAGS "${CMAKE_SHARED_LINKER_FLAGS} -flto")
else()
	add_definitions(-DDEFAULT_LOG_LEVEL=${DEFAULT_LOG_LEVEL}) # no quotes because it is a C-macro
endif()

# Fix compile time logging
if(CMAKE_BUILD_TYPE MATCHES Release AND CONSTANT_LOG_LEVEL)
    message("*** Runtime logging disabled! ***")
	add_definitions(-DCONSTANT_LOG_LEVEL)
else()
    message("*** Runtime logging enabled! ***")
endif()

# Enable testing
if(ENABLE_TESTING)
    message("*** Testing enabled! ***")
	include(CTest)
	enable_testing()
    add_definitions(-DTEST)
else()
    message("*** Testing disabled! ***")
endif()

# Enable security flags
# These come after build type as they may override the given flags
if(ENABLE_SECURITY)
	message(WARNING "Security mode enabled. Overriding other options!")
	if(ENABLE_MEMCHECK)
		message(FATAL_ERROR "ENABLE_SECURITY and ENABLE_MEMCHECK are mutually exclusive")
	endif()

	# Security flags
	set(SECURITY_FLAGS
		"-m64"
		"-fsanitize=address"
		"-D_GLIBCXX_ASSERTIONS"
		"-fstack-protector-all"
		"-Wstack-protector"
		"--param ssp-buffer-size=4"
		"-pie"
		"-fPIE"
		"-ftrapv"
		"-D_FORTIFY_SOURCE=2"
		"-O2"
		"-Wl,-z,relro,-z,now"
		"-Wl,-z,noexecstack"
		"-Wformat -Wformat-security"
		# "-fvtable-verify=std" # Requires custom gcc compilation with this flag enabled.
	)
	string(REPLACE ";" " " SECURITY_FLAGS "${SECURITY_FLAGS}")

	# Since we are overriding already set flags, we must set them depending on build type
	# Build type flags are appended to the default flags, so if they are used we append to them
	# directly instead of appending to the default flags, to ensure these overrides work
	if(CMAKE_BUILD_TYPE MATCHES Debug)
		set(CMAKE_CXX_FLAGS_DEBUG "${CMAKE_CXX_FLAGS_DEBUG} ${SECURITY_FLAGS}")
		set(CMAKE_C_FLAGS_DEBUG   "${CMAKE_C_FLAGS_DEBUG}   ${SECURITY_FLAGS}")
	elseif(CMAKE_BUILD_TYPE MATCHES Release)
		set(CMAKE_CXX_FLAGS_RELEASE "${CMAKE_CXX_FLAGS_RELEASE} ${SECURITY_FLAGS}")
		set(CMAKE_C_FLAGS_RELEASE   "${CMAKE_C_FLAGS_RELEASE}   ${SECURITY_FLAGS}")
	else()
		set (CMAKE_C_FLAGS   "${CMAKE_C_FLAGS}   ${SECURITY_FLAGS}")
		set (CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${SECURITY_FLAGS}")
	endif()

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

	# For make clean
	set_property(TARGET "${DOC_MAKE_TARGET}"
		APPEND PROPERTY ADDITIONAL_CLEAN_FILES
		"${DOXYGEN_OUTPUT_DIRECTORY}"
		"${DOXYGEN_OUT}"
	)

endif(BUILD_DOC)


#################################################
#                                               #
#          Generate library and tests           #
#                                               #
#################################################


# Create a make target for the library
add_subdirectory("${LIBRARY_SRC}")

# Create a make target for test cases
if(ENABLE_TESTING)
	add_subdirectory(./tests)
endif()
