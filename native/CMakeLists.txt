cmake_minimum_required( VERSION 3.16 )

# Append to the cmake search path
# This allows for simple invoking of cmake files in this path
list(APPEND CMAKE_MODULE_PATH "${CMAKE_CURRENT_SOURCE_DIR}/cmake")

# Help with user config
include(set_prefer_cli)


#################################################
#                                               #
#                  Set by User                  #
#                                               #
#################################################


# Config options
option( BUILD_DOC "Create a make target for documentation"   ON )
option( ENABLE_TESTING "Create a make target for test cases" ON )
option( OPTIMIZE_FOR_NATIVE "Build with -march=native etc"   OFF )
option( ENABLE_ANSI_COLOR_CODES "Enable ansi color codes"    ON )


#################################################
#                                               #
#               Set by Developer                #
#                                               #
#################################################


### Constants ###

# Shared library name
set( CLARICPP "claricpp" )

# API Version
# This is different from version which is read from /VERSION
set( SOVERSION 1 )

# Run make <DOC_MAKE_TARGET> to build documentation if BUILD_DOC is ON
# Running make <DOC_MAKE_TARGET> generates html, latex, and man pages
set( DOC_MAKE_TARGET "docs" )

# Default build type
# Default to debug mode
# Use cache to override defaults
# Can override this by running cmake with "-DCMAKE_BUILD_TYPE=Release"
set( CMAKE_BUILD_TYPE "Debug" CACHE STRING "Cmake build type" )

# Log levels are defined in ./src/utils/log/level/level/hpp
# Note: Lower log levels implier higher levels (i.e. verbose implies critical)
set( DEFAULT_RELEASE_LOG_LEVEL "Warning" )
set( DEFAULT_DEBUG_LOG_LEVEL "Debug" )
set( DEFAULT_OTHER_LOG_LEVEL "Info" )

### Config Options ###

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
option( CONSTANT_LOG_LEVEL "Force log level to be set at compiletime for release builds" OFF )

# Security Options
# These options will overide any previously set option if enabled
option( ENABLE_SECURITY "Build with security flags at the cost of runtime performance" OFF )
option( ENABLE_CET "Builds with CET fcf-protection, requires ENABLE_SECURITY" OFF )


#################################################
#                  Z3 Options                   #
#################################################


# The name of the z3 make target
set( Z3_MAKE_TARGET "z3" )

# The name of the z3 library target (this is different from the make target)
# The make target triggers this target to be built; this is the library claricpp should link to
# This has to be distinct from the make target because cmake will
# not export imported shared library targets to the build system
set( Z3_LIB_PRIVATE_TARGET "lib-z3" )

# Defines how the z3 library is acquired
# The supported options are:
#  SYSTEM   - Looks for a z3 library in common library directories
#  DOWNLOAD - Download and extract a compressed directory given a URL
#  PATH     - Define the library to be loaded from some file path
#  BUILD    - Build z3 either from a local directory or git link (local will be prioritized)
# Note that for all modes, the output must be a directory containing a 'bin' and 'include' directory
# The 'bin' directory should include the shared library claricpp can link to
# The 'include' directory should include the header files claricpp can use
set_prefer_cli( Z3_ACQUISITION_MODE BUILD )

# This option is used to help locate the Z3 library.
# If left undefined cmake will attempt to locate it automatically
# If necessary, a message will be printed out explaining this variable should be set
#set(Z3_LIB_EXTENSION ".so")


# Depending on the mode selected, only one of the groups of options below will be relevant


#########################
### Z3 System Options ### (Only relevant if Z3_ACQUISITION_MODE is SYSTEM)
#########################

if (Z3_ACQUISITION_MODE STREQUAL SYSTEM)

	# The path to the include directory (z3 header files)
	# This directory will by symlinked into the build directory for read-only usage
	# Claricpp is coded to use z3 headers as non-system headers, so this is necessary
	set_prefer_cli( Z3_INCLUDE_PATH "/path/to/z3-headers/" )

endif()

#########################
## Z3 Download Options ## (Only relevant if Z3_ACQUISITION_MODE is DOWNLOAD)
#########################

if (Z3_ACQUISITION_MODE STREQUAL DOWNLOAD)

	# The link to download z3 from
	# The link must be the compressed z3 install directory containing 'bin' and 'include'
	set_prefer_cli( Z3_DOWNLOAD_LINK
		# "https://github.com/Z3Prover/z3/releases/download/z3-4.8.10/z3-4.8.10-x64-ubuntu-18.04.zip"
		"https://github.com/Z3Prover/z3/releases/download/z3-4.8.10/z3-4.8.10-x64-osx-10.15.7.zip"
	)

	# Optionally provide the hash of the compressed file
	# If this is done, the hash will be checked after download for security
	# If this is not desired, leave these variable undefined
	set_prefer_cli( Z3_DOWNLOAD_HASH "750773630d05cc7c6e4e92be937bfdc6" )
	set_prefer_cli( Z3_DOWNLOAD_HASH_TYPE "MD5" )

	# Other required download settings
	option( Z3_DOWNLOAD_TLS_VERIFY "Specify whether to verify the server certificate for https:// urls" ON )
	option( Z3_DOWNLOAD_SHOW_PROGRESS "Show download progress while downloading." OFF )
	set( Z3_DOWNLOAD_TIMEOUT_SECONDS 120 )

endif()

#####################
## Z3 Path Options ## (Only relevant if Z3_ACQUISITION_MODE is PATH)
#####################

if (Z3_ACQUISITION_MODE STREQUAL PATH)

	# The path to the Z3 library
	# On Mac this will probably be a dynamic library (.dylib)
	# On Linux this will probably be a shared object (.so)
	# On Windows this will probably be a dynamic link library (.dll)
	set_prefer_cli( Z3_LIB_PATH "/path/to/z3/library.so" )

	# The path to the include directory (z3 header files)
	# This directory will by symlinked into the build directory for read-only usage
	# Claricpp is coded to use z3 headers as non-system headers, so this is necessary
	set_prefer_cli( Z3_INCLUDE_PATH "/path/to/z3-headers/" )

endif()

######################
## Z3 Build Options ## (Only relevant if Z3_ACQUISITION_MODE is BUILD)
######################

if (Z3_ACQUISITION_MODE STREQUAL BUILD)

	# If false, rebuilds will not occur if libz3 is present during configuration
	# Note: It is reccomended you reconfigure cmake after a libz3 build otherwise
	# libz3 may re-build every time make is invoked as it is using an old configuration
	option( Z3_FORCE_REBUILD "If false, rebuilds will not occur if libz3 is present during configuration" OFF )

	# Specify the repo and commit that should be used to build Z3
	# Z3_GIT_COMMIT can be a branch, tag, or commit hash
	set_prefer_cli( Z3_REPO_LINK "https://github.com/Z3Prover/z3" )
	set_prefer_cli( Z3_GIT_COMMIT "master" )

	# Build z3 in release or debug mode
	option( Z3_BUILD_RELEASE_MODE "ON to build z3 in release mode, OFF for debug mode" ON )

	# The number of cores used to compile z3 (think of this as make -j<this>)
	# Note: this will override whatever is passed to make during the build
	# This is because make doesn't give a way for subprocess builds to reuse this job limit
	if(NOT DEFINED Z3_NUM_CORES)
		include(ProcessorCount)
		ProcessorCount(Z3_NUM_CORES)
		math(EXPR Z3_NUM_CORES "${Z3_NUM_CORES}-2") # Set Z3_NUM_CORES to: $(nproc) - 2
	endif()

endif()

#################################################
#                                               #
#               Program Constants               #
#                                               #
#################################################


# Define the project
project("${CLARICPP}" C CXX)

# Define standards
set(CMAKE_C_STANDARD 11)
set(CMAKE_CXX_STANDARD 17)
set(CMAKE_C_EXTENSIONS OFF)
set(CMAKE_CXX_EXTENSIONS OFF)
set(CMAKE_C_STANDARD_REQUIRED ON)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

# Define the version
file(READ "../VERSION" VERSION)
string(STRIP "${VERSION}" VERSION)

# Library source
# Used for compilation and header lookup for tests
set(CLARICPP_SRC "${CMAKE_CURRENT_SOURCE_DIR}/src")


#################################################
#                                               #
#    Pre SO Target Definition Configuration     #
#                                               #
#################################################


# Find Required
include(z3)

# Static Anaylsis
include(StaticAnalsis)

# Documentation
if(BUILD_DOC)
	include(Doxygen)
endif()

# Global definitions
if(ENABLE_ANSI_COLOR_CODES)
	add_definitions("-DENABLE_ANSI_COLOR_CODES")
endif()

# Remap file prefixes to make source location irrelevant to __FILE__, etc.
# This is *required* as we calculate class unique IDs based off the normalized
# path acquired by processing the __FILE__ macro. Anything that uses any headers
# with a class unique ID *must* include this flag otherwise we may end up with
# silent ODR violations as the calculated values of the CUIDs may differ from
# the ones inlined in the shared library. Furthermore, other compilation which
# used the headers may not move the headers within this directory for the same
# reason: it changes the normpath of __FILE__ which changes the CUIDs, etc.
add_compile_options("-ffile-prefix-map=${CMAKE_SOURCE_DIR}/=/")

# Global required complication flags
add_compile_options(
	# Warning globs
	"-Wall"
	"-Wextra"
	"-Werror" # Convert warnings to errors
	# A bunch of useful warnings to have
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
	"-Wsign-promo"
	"-Wstrict-aliasing=1" # Improves upon Wall's level 3
	"-Wstrict-overflow=5" # Improves upon Wall's level 1
	"-Wswitch-default"
	"-Wswitch-enum"
	"-Wundef"
	"-Wunreachable-code"
	"-Wunused"
	"-Wunused-parameter"
	"-Wvariadic-macros"
	"-Wwrite-strings"
	"-Wnull-dereference"
	"-Wdouble-promotion"
	"-Wnon-virtual-dtor"
	"-Wreserved-id-macro"
	"-Wreserved-user-defined-literal"
)

# Treat #warning's as warnings
if(CMAKE_CXX_COMPILER_ID STREQUAL "GNU")
	add_compile_options("-Wno-error=cpp")
elseif(CMAKE_CXX_COMPILER_ID MATCHES "Clang")
	add_compile_options("-Wno-error=#warnings")
else()
	message(WARNING "Unknown compiler, please manually add a compile flag"
					"to ensure that #warnings are not caught by -Werror.")
endif()

# Compile options that cannot be used with clang
if(CMAKE_CXX_COMPILER_ID STREQUAL "GNU")
	if(CLANG_TIDY)
		message(WARNING "Clang (from clang-tidy) cannot handle gcc specific warning options."
						"Disabling them to allow clang-tidy to function.")
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
	add_compile_options("-EHsc")
endif()


#################################################
#                                               #
#               Target Definition               #
#                                               #
#################################################


# Note: This should be the last program constant
# Non-target specific things *must* be defined before this for them to affect this
add_library("${CLARICPP}" SHARED)


#################################################
#                                               #
#             Option Configuration              #
#                                               #
#################################################


# Option verification
if(ENABLE_MEMCHECK AND APPLE AND NOT ALLOW_NO_MEMCHECK_APPLE)
	message(FATAL_ERROR "Memcheck is not compatible with the lastest versions of MacOS")
endif()

# Enable good coding checks as actual warnings
if(NOT EFFECTIVE_CPP_STYLE_CHECK) # TODO
	target_compile_options("${CLARICPP}" PUBLIC
		"-Weffc++" # Enforces a few generally good C++ coding practices
		"-Wno-error=effc++" # Allow effc++ warnings to remain warnings
	)
endif()


# Optimize for native code
if(OPTIMIZE_FOR_NATIVE)
	target_compile_options("${CLARICPP}" PRIVATE
		"-march=native"
		"-mtune=native"
	)
endif()

# Fix compile time logging
if(CMAKE_BUILD_TYPE MATCHES Release AND CONSTANT_LOG_LEVEL)
    message("Runtime logging disabled!")
	target_compile_definitions("${CLARICPP}" PUBLIC "CONSTANT_LOG_LEVEL") # Export this macro
else()
    message("Runtime logging enabled!")
endif()

# Enable testing
if(ENABLE_TESTING)
    message("Testing enabled!")
	include(CTest)
	enable_testing()
	# Macros
	target_compile_definitions("${CLARICPP}" PUBLIC "ENABLE_TESTING") # Export this macro
else()
    message("Testing disabled!")
endif()

# Build type
if(CMAKE_BUILD_TYPE MATCHES Debug)
    message("Debug Mode enabled!")
	target_compile_definitions("${CLARICPP}"
		PUBLIC "DEFAULT_LOG_LEVEL=${DEFAULT_DEBUG_LOG_LEVEL}" # Export this macro
		PUBLIC "DEBUGMODE=1"
		PUBLIC "DEBUG=1"
	)
	# Macros
	target_compile_definitions("${CLARICPP}" PUBLIC "_GLIBCXX_ASSERTIONS")
	# Compile flags
	target_compile_options("${CLARICPP}" PUBLIC
		"-O0"
		"-g"
		"-fasynchronous-unwind-tables"
		"-grecord-gcc-switches"
	)
elseif(CMAKE_BUILD_TYPE MATCHES Release)
    message("Release Build enabled!")
	target_compile_definitions("${CLARICPP}" PUBLIC  # Export this macro
		"DEFAULT_LOG_LEVEL=${DEFAULT_RELEASE_LOG_LEVEL}"
	)
	# Compilation and linker flags
	target_compile_options("${CLARICPP}" PRIVATE "-pipe" "-O3")
	target_link_options("${CLARICPP}" PRIVATE "-flto")
else()
	message(WARNING "Build level: ${CMAKE_BUILD_TYPE}")
	target_compile_definitions("${CLARICPP}" PUBLIC # Export this macro
		"DEFAULT_LOG_LEVEL=${DEFAULT_OTHER_LOG_LEVEL}"
	)
endif()

# Enable security flags
# These come after build type as they may override the given flags
if(ENABLE_SECURITY)
	message(WARNING "Security mode enabled. Overriding other options!")
	include(EnableSecurity)
endif()


#################################################
#                                               #
#          Generate Library and Tests           #
#                                               #
#################################################


# Create a make target for the library
add_subdirectory("${CLARICPP_SRC}")

# Allow building with z3
target_include_directories("${CLARICPP}"
	SYSTEM BEFORE
	PRIVATE "${Z3_INCLUDE_DIR}"
)
target_link_libraries("${CLARICPP}" PRIVATE "${Z3_LIB_PRIVATE_TARGET}")

# Configure library compilation and linking
# This is just in case we missed any flags above
if(CMAKE_BUILD_TYPE MATCHES Release)
	set_property(TARGET "${CLARICPP}"
		PROPERTY INTERPROCEDURAL_OPTIMIZATION TRUE
	)
endif()

# Create a make target for test cases
if(ENABLE_TESTING)
	add_subdirectory(tests)
endif()
