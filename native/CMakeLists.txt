cmake_minimum_required( VERSION 3.18 )

# Append our ./cmake script directory to the cmake path then run includes
list(APPEND CMAKE_MODULE_PATH "${CMAKE_CURRENT_SOURCE_DIR}/cmake")
include(config_cmake)
include(default)


#################################################
#                                               #
#                  Set by User                  #
#                                               #
#################################################


# Config options
option( BUILD_API "Create a make target for the python API" ON )
option( BUILD_DOC "Create a make target for documentation"  ON )
option( BUILD_TESTS "Create a make targets for test cases"  ON )
option( OPTIMIZE_FOR_NATIVE "Build with -march=native etc"  OFF )
option( ENABLE_ANSI_COLOR_CODES "Enable ansi color codes"   ON )


# Where the the library source will be installed
# This source will be parsed by backtraces for code snippits
# Set this to empty if dynamic configuration is preferred (ex. building with setup.py)
default(SOURCE_ROOT_FOR_BACKTRACE "${CMAKE_CURRENT_SOURCE_DIR}")


#################################################
#                                               #
#               Set by Developer                #
#                                               #
#################################################


### Constants ###

# Shared library name
default( CLARI "clari" )
message("Library name: ${CLARI}")

# Run make <DOC_MAKE_TARGET> to build documentation if BUILD_DOC is ON
# Running make <DOC_MAKE_TARGET> generates html, latex, and man pages
set( DOC_MAKE_TARGET "docs" )

# Default build type
# Default to debug mode
# Use cache to override defaults
# Can override this by running cmake with "-DCMAKE_BUILD_TYPE=RelWithDebugInfo" or Release
set( CMAKE_BUILD_TYPE "Debug" CACHE STRING "Cmake build type" )
if (BUILD_TESTS AND NOT CMAKE_BUILD_TYPE MATCHES "Debug" )
	message(FATAL_ERROR "Tests not supported for release build due to pybind11 linkage visibility")
endif()

# Log levels are defined in ./src/utils/log/level/level/hpp
# Note: Lower log levels implier higher levels (i.e. verbose implies critical)
default( DEFAULT_RELEASE_LOG_LEVEL "warning" )
default( DEFAULT_DEBUG_LOG_LEVEL "debug" )
default( DEFAULT_OTHER_LOG_LEVEL "info" )

### Config Options ###

# VERSION
default( VERSION "" )
# If VERSION is empty the VERSION is read from this
default( VERSION_FILE "${CMAKE_CURRENT_SOURCE_DIR}/../VERSION" )

# Static Analysis Options
option( IWYU "Enable iwyu" OFF )
option( LWYU "Enable lwyu" ON )
option( CPP_CHECK "Enable cppcheck" OFF )
option( CLANG_TIDY "Enable clang-tidy" ON )

# Config options
option( CMAKE_VERBOSE_MAKEFILE "Enable make VERBOSE=1 by default" OFF )
# This is useful for IDEs, developer tools, and for doxygen documentation generation
option( CMAKE_EXPORT_COMPILE_COMMANDS "Exports a json useful to IDEs and other tools" ON )
# These warnings will not cause errors; as we do not strictly adhere to them all
option( EFFECTIVE_CPP_STYLE_CHECK "Enable effective C++ style checks as warnings" ON )
# The memcheck and security options are mutually exclusive
# Memcheck cannot run with security enabled
option( ENABLE_MEMCHECK "Enable memcheck on test target" ON )
option( ALLOW_NO_MEMCHECK_APPLE "Allow not using memcheck on apple" ON )
# If enabled: log calls to log levels lower than defined will have no performance penalty
option( CONSTANT_LOG_LEVEL "Force log level to be set at compile time" OFF )

# Security Options
# These options will overide any previously set option if enabled
option( ENABLE_SECURITY "Build with security flags at the cost of runtime performance" OFF )
option( ENABLE_CET "Builds with CET fcf-protection, requires ENABLE_SECURITY" OFF )

# Override what the compiler says about it handling RTTI
default(RTTI_OVERRIDE FALSE)

### Z3 Options ###

# The path to the Z3 root (must contain a lib and include directory)
# Might look like ~/.virtualenvs/claripy/lib/python3.11/site-packages/z3
default( Z3_ROOT "/path/to/z3/" )

### Backward Options ###

# Require backend to use a backend lib
# The backend lib provides a lot more information if available
default(REQUIRE_BACKWARD_BACKEND FALSE)

### Boost Options ###

# If the GMP headers boost uses are not installed in the normal path, set this
# This variable is ignored if it is empty
default(GMP_INCLUDE_DIR "")

# The default boost include location
# This variable is ignored if empty and will be populated by find_package
# Note: The casing on this is intentional, this is the variable find_package uses
# Note: This may not be non-empty if BOOST_URL is
default(Boost_INCLUDE_DIRS "")

# A URL to download boost from
# If empty find_package will not be used
# Ex. https://boostorg.jfrog.io/artifactory/main/release/1.66.0/source/boost_1_66_0.tar.gz
# Note: This may not be non-empty if Boost_INCLUDE_DIRS is
default(BOOST_URL "")

# An optional hash algorithm and hash the download should have
# Ignored if empty of if BOOST_URL is empty
# Ex. "sha256=94ced8b72956591c4775ae2207a9763d3600b30d9d7446562c552f0a14a63be7"
default(BOOST_HASH_CHECK "")

# The directory to create and store boost in
# Ignored if BOOST_URL is empty
default(BOOST_DIR "${CMAKE_CURRENT_SOURCE_DIR}/boost")

# Force a clean download of boost
# Does not matter if BOOST_URL is not ""
default(BOOST_FORCE_CLEAN_DOWNLOAD OFF)


#################################################
#                                               #
#               Program Constants               #
#                                               #
#################################################


# Define the project
project("${CLARI}" C CXX)

# Define standards
set(CMAKE_C_STANDARD 11)
set(CMAKE_CXX_STANDARD 17)
set(CMAKE_C_EXTENSIONS OFF)
set(CMAKE_CXX_EXTENSIONS OFF)
set(CMAKE_C_STANDARD_REQUIRED ON)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

# Define the version (allow overrides by setting VERSION)
if (VERSION STREQUAL "")
	if (EXISTS "${VERSION_FILE}")
		message(STATUS "Loading version from version file: ${VERSION_FILE}")
		file(READ "${VERSION_FILE}" VERSION)
		string(STRIP "${VERSION}" VERSION)
	else()
		message(WARNING "Version file ${VERSION_FILE} missing.")
		set(VERSION "Unknown")
	endif()
endif()
message(STATUS "Version: ${VERSION}")

# The API version (on macOS: the compatability version; we support only the current one)
default( SOVERSION "${VERSION}" )


#################################################
#                                               #
#    Pre SO Target Definition Configuration     #
#                                               #
#################################################


# BigInt support
include(Boost)
include(GMP) # Boost multiprecision backend

# Other dependencies
include(Backward)
set(Z3_INCLUDE_DIR "${Z3_ROOT}/include")
find_library(Z3_LIBRARY z3 PATHS "${Z3_ROOT}/lib" REQUIRED NO_DEFAULT_PATH)

# Static Analysis
include(StaticAnalsis)

# Documentation
if(BUILD_DOC)
	include(Doxygen)
endif()

# Global definitions
if(ENABLE_ANSI_COLOR_CODES)
	add_definitions("-DENABLE_ANSI_COLOR_CODES")
endif()

# API
# Currently we add a subdir to ensure a desired version (could be a fork as needed)
set(PYBIND11_FINDPYTHON ON)
add_subdirectory(pybind11)

# Remap file prefixes to make source location irrelevant to __FILE__, etc.
# This is *required* as we calculate class unique IDs based off the normalized
# path acquired by processing the __FILE__ macro. Anything that uses any headers
# with a class unique ID *must* include this flag otherwise we may end up with
# silent ODR violations as the calculated values of the CUIDs may differ from
# the ones inlined in the shared library. Furthermore, other compilation which
# used the headers may not move the headers within this directory for the same
# reason: it changes the normpath of __FILE__ which changes the CUIDs, etc.
add_compile_options("-ffile-prefix-map=${CMAKE_CURRENT_SOURCE_DIR}/=/")

# Convert warnings to errors but treat #warning's as warnings
add_compile_options("-Werror")
if(CMAKE_CXX_COMPILER_ID STREQUAL "GNU")
	add_compile_options("-Wno-error=cpp")
elseif(CMAKE_CXX_COMPILER_ID MATCHES "Clang")
	add_compile_options("-Wno-error=#warnings")
else()
	message(WARNING "Unknown compiler, please manually add a compile flag"
			"to ensure that #warnings are not caught by -Werror.")
endif()

# Global required compilation flags
add_compile_options(
	"-g"
	"-Wall"
	"-Wextra"
	"-Wcast-align"
	"-Wcast-qual"
	"-Wdeprecated"
	"-Wconversion"
	"-Wdisabled-optimization"
	"-Wformat-nonliteral"
	"-Wformat-security"
	"-Wformat-y2k"
	"-Wformat=2"
	"-Wimport"
	"-Winit-self"
	"-Winvalid-pch"
	"-Wmissing-field-initializers"
	"-Wmissing-format-attribute"
	"-Wmissing-include-dirs"
	"-Wmissing-noreturn"
	"-Wold-style-cast"
	"-Woverloaded-virtual"
	"-Wpacked"
	"-Wpointer-arith"
	"-Wredundant-decls"
	"-Wshadow"
	"-Wsign-conversion"
	"-Wstrict-aliasing=1" # Improves upon Wall's level 3
	"-Wstrict-overflow=5" # Improves upon Wall's level 1
	"-Wswitch-default"
	"-Wswitch"
	"-Wundef"
	"-Wunreachable-code"
	"-Wunused"
	"-Wunused-parameter"
	"-Wvariadic-macros"
	"-Wwrite-strings"
	"-Wnull-dereference"
	"-Wdouble-promotion"
	"-Wnon-virtual-dtor"
)

# Compile options that cannot be used with g++
if(NOT CMAKE_CXX_COMPILER_ID STREQUAL "GNU")
	add_compile_options(
		"-Wreserved-id-macro"
		"-Wreserved-user-defined-literal"
	)
endif()

# Compile options that cannot be used with clang
if(NOT CMAKE_CXX_COMPILER_ID MATCHES "(C|c?)lang")
	if(CLANG_TIDY)
		message(WARNING "Clang (from clang-tidy) cannot handle gcc specific warning options."
						" Disabling them to allow clang-tidy to function.")
	else()
		add_compile_options(
			"-Wsuggest-override"
			"-Wsuggest-final-types"
			"-Wsuggest-final-methods"
			"-Wstrict-null-sentinel"
			"-Wlogical-op"
			"-Wnoexcept"
		)
	endif()
endif()

# MSVC enable exceptions
if(CMAKE_CXX_COMPILER_ID STREQUAL "MSVC")
	add_compile_options("-EHsc") # Allow C++ exceptions
endif()

# Allow linking to claricpp for testing purposes when built with debug
# This should not be done for release builds, pybind11 items should be hidden!
# Specifically, pybind11 might force -fvisibility=hidden
if(CMAKE_BUILD_TYPE MATCHES Debug)
	set(CMAKE_CXX_VISIBILITY_PRESET "default")
	add_compile_options("-Wno-error=attributes")
	message("Allowing attrbute warnings are not errors in debug mode; they allow testing.")
endif()


#################################################
#                                               #
#               Target Definition               #
#                                               #
#################################################


# Note: This should be the last program constant
# Non-target specific things *must* be defined before this for them to affect this
if(CMAKE_BUILD_TYPE MATCHES Debug)
	pybind11_add_module("${CLARI}" SHARED)
else()
	pybind11_add_module("${CLARI}")
endif()


#################################################
#                                               #
#             Option Configuration              #
#                                               #
#################################################


# Option verification
if(ENABLE_MEMCHECK AND APPLE AND NOT ALLOW_NO_MEMCHECK_APPLE)
	message(FATAL_ERROR "Memcheck is not compatible with the latest versions of MacOS")
endif()

# Enable good coding checks as actual warnings
if(NOT EFFECTIVE_CPP_STYLE_CHECK)
	target_compile_options("${CLARI}" PUBLIC
		"-Weffc++" # Enforces a few generally good C++ coding practices
		"-Wno-error=effc++" # Allow effc++ warnings to remain warnings
	)
endif()

# Optimize for native code
if(OPTIMIZE_FOR_NATIVE)
	target_compile_options("${CLARI}" PRIVATE
		"-march=native"
		"-mtune=native"
	)
endif()

# RTTI override
if(RTTI_OVERRIDE)
	message("RTTI_OVERRIDE enabled; forcibly assuming compiler supports RTTI")
	target_compile_definitions("${CLARI}" PUBLIC "RTTI_OVERRIDE") # Export this macro
endif()

# Fix compile time logging
if(CONSTANT_LOG_LEVEL)
    message("Constant log level set!")
	target_compile_definitions("${CLARI}" PUBLIC "CONSTANT_LOG_LEVEL") # Export this macro
else()
    message("Runtime adjustable log level enabled!")
endif()

# Enable testing
if(BUILD_TESTS)
	target_compile_definitions("${CLARI}" PUBLIC "BUILD_TESTS") # Export this macro
endif()

# Build type
if(CMAKE_BUILD_TYPE MATCHES Debug)
    message("Debug Mode enabled!")
	target_compile_definitions("${CLARI}"
		PUBLIC "DEFAULT_LOG_LEVEL=${DEFAULT_DEBUG_LOG_LEVEL}" # Export this macro
		PUBLIC "_GLIBCXX_ASSERTIONS" # Export this macro
		PUBLIC "DEBUGMODE=1" # Export this macro
		PUBLIC "DEBUG=1" # Export this macro
	)
	target_compile_options("${CLARI}" PUBLIC
		"-O0"
		"-fasynchronous-unwind-tables"
		"-grecord-gcc-switches"
	)
	target_link_options("${CLARI}" PUBLIC
		"-rdynamic"
	)
elseif(CMAKE_BUILD_TYPE MATCHES Rel) # Release / RelWithDebugInfo
    message("Release Build enabled!")
	target_compile_definitions("${CLARI}"
		 PUBLIC "DEFAULT_LOG_LEVEL=${DEFAULT_RELEASE_LOG_LEVEL}" # Export this macro
	)
	# Compilation and linker flags
	target_compile_options("${CLARI}" PRIVATE "-pipe" "-O3")
else()
	message(WARNING "Build level: ${CMAKE_BUILD_TYPE}")
	target_compile_definitions("${CLARI}"
		PUBLIC "DEFAULT_LOG_LEVEL=${DEFAULT_OTHER_LOG_LEVEL}" # Export this macro
	)
endif()

# Enable security flags
# These come after build type as they may override the given flags
if(ENABLE_SECURITY)
	message(WARNING "Security mode enabled. Overriding other options!")
	include(enable_security)
	enable_security("${CLARI}" "${ENABLE_MEMCHECK}" "${ENABLE_CET}")
endif()

# Configure library compilation and linking
# This is just in case we missed any flags above
if(CMAKE_BUILD_TYPE MATCHES Rel)
	include(CheckIPOSupported)
	check_ipo_supported(RESULT IPO_SUPPORTED OUTPUT IPO_ERROR)
	if (IPO_SUPPORTED)
		message(STATUS "Interprocedural optimization enabled")
		target_link_options("${CLARI}" PRIVATE "-flto")
		set_property(TARGET "${CLARI}" PROPERTY INTERPROCEDURAL_OPTIMIZATION TRUE)
	else()
		message(WARNING "Interprocedural optimization is not supported: ${IPO_ERROR}")
		message("Disabling interprocedural optimization")
	endif()
endif()


#################################################
#                                               #
#          Generate Library and Tests           #
#                                               #
#################################################


# Library source
add_subdirectory(src)

# Backtrace config
add_backward("${CLARI}" TRUE)

# Z3 config
target_include_directories("${CLARI}"
	SYSTEM BEFORE
	PUBLIC "${Z3_INCLUDE_DIR}"
	PUBLIC ${Boost_INCLUDE_DIRS}
)
if (NOT GMP_INCLUDE_DIR STREQUAL "")
	target_include_directories("${CLARI}" SYSTEM BEFORE PUBLIC "${GMP_INCLUDE_DIR}")
endif()
target_link_libraries("${CLARI}"
	PUBLIC "${Z3_LIBRARY}"
	PUBLIC "${GMP_LIBRARIES}" # Boost multiprecision backend
	# PUBLIC dl (only necessary if using native backtraces; Backward handles it's own dependencies)
)

# Enable testing
if(BUILD_TESTS)
	include(CTest)
	enable_testing()
	message("Testing enabled!")
	add_subdirectory(tests)
else()
	message("Testing disabled!")
endif()
