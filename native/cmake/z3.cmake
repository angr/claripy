# This file configures a make target for z3, which other targets can depend on
# Relevant epoxrted variables:
#
#  Z3_LIB_TARGET - The name of the z3 target
#  Z3_INCLUDE_DIR - The directory containing the headers linked targets may wish to include

# TODO: avoid polluting native directory with z3?


#################################################
#               Set by developer                #
#################################################


# The link to the Z3 repo / commit
# If a local z3 directory exists it will be prefferred to this
set( Z3_REPO_LINK "https://github.com/Z3Prover/z3" )
set( Z3_GIT_COMMIT "517d907567f4283ad8b48ff9c2a3f6dce838569e" )

# The name of the built shared object
# Note: This depends on the repo being built
set( Z3_LIB_SO_NAME "z3.so" )

# Define the location of the z3 directory
set( Z3_DIR "${CMAKE_SOURCE_DIR}/z3/" )


#################################################
#                 Configuration                 #
#################################################


# Dependencies
include(ExternalProject)
include(ProcessorCount)

# Define various z3 sub-directories
set( Z3_INSTALL_DIR "${Z3_DIR}/build/install/" )
set( Z3_INCLUDE_DIR "${Z3_INSTALL_DIR}/include/") # Required by name outside of this file
set( Z3_LIB_DIR "${Z3_INSTALL_DIR}/lib/" )
set( Z3_LIB "${Z3_LIB_DIR}/${Z3_LIB_SO_NAME}" )


# The Z3 library target
set( Z3_LIB_TARGET "z3" ) # Required by name outside of this file
add_library( "${Z3_LIB_TARGET}"
	SHARED
	IMPORTED
	GLOBAL # Scopes the library outside of its directory
)
set_property(TARGET "${Z3_LIB_TARGET}" PROPERTY
	IMPORTED_LOCATION "${Z3_LIB}"
)

# If a local z3 dir exists, override download command with an empty string
if(EXISTS "${Z3_DIR}")
	message(WARNING "Existing z3 directory found. Prioritizing it over a fresh clone.")
	set(SKIP_DOWNLOAD_IF_EXISTS DOWNLOAD_COMMAND "") # Unquoted is needed here
else()
	message("No existing z3 directory found. Cloning a new one.")
endif()

# Locate the system's make program
# Define the arguments to be passed to it
# If no suitable program is found, report so and error out
find_program(Z3_MAKE_EXE NAMES gmake make)
if (Z3_MAKE_EXE MATCHES "-NOTFOUND$")
	find_program(MAKE_EXE NAMES nmake)
	if (Z3_MAKE_EXE MATCHES "-NOTFOUND$")
		message(FATAL_ERROR "No suitable make program found.")
	endif()
	set(Z3_MAKE_ARGS) # Empty args, no parallelization args for nmake
else()
	ProcessorCount(Z3_NUM_CORES)
	math(EXPR Z3_NUM_CORES "${Z3_NUM_CORES}-2")
	message( WARNING
		"Because make doesn't expose the number of jobs it is allowed to use,"
		" Z3 will be built with the number of cores on the system minus two. "
		" That is, Z3 will be built with ${Z3_NUM_CORES} cores."
	)
	set(Z3_MAKE_ARGS "-j${Z3_NUM_CORES}")
endif()

# Define Z3 as an external project
set( Z3_BUILDER "z3_build" )
ExternalProject_Add("${Z3_BUILDER}"
	# Download options
	${SKIP_DOWNLOAD_IF_EXISTS} # This should *not* be quoted
	GIT_REPOSITORY "${Z3_REPO_LINK}"
	GIT_TAG "${Z3_GIT_COMMIT}"
	GIT_CONFIG "advice.detachedHead=false" # Silence unneeded warnings
	GIT_SHALLOW TRUE                       # We don't need a deep clone
	GIT_PROGRESS TRUE                      # Show progress while cloning
	# Where to put the z3 directory
	PREFIX "${Z3_DIR}"
	BUILD_COMMAND "${Z3_MAKE_EXE}" ${Z3_MAKE_ARGS} # The second one must be unquoted
	CMAKE_CACHE_ARGS
		"-DZ3_SINGLE_THREADED:BOOL=FALSE"
		"-DZ3_INCLUDE_GIT_HASH:BOOL=TRUE"
		# Build Options
		"-DCMAKE_BUILD_TYPE:STRING=Release"
		"-DZ3_BUILD_LIBZ3_SHARED:BOOL=TRUE"
		"-DZ3_LINK_TIME_OPTIMIZATION:BOOL=TRUE"
		"-DWARNINGS_AS_ERRORS:STRING=SERIOUS_ONLY"
		# Install Options
		"-DCMAKE_INSTALL_INCLUDEDIR:PATH=${Z3_INCLUDE_DIR}" # Absolute path
		"-DCMAKE_INSTALL_LIBDIR:PATH=${Z3_LIB_DIR}"         # Absolute path
		# This should never be used, but just in case:
		"-DCMAKE_INSTALL_PREFIX:PATH=${Z3_INSTALL_DIR}"
		# Disable Unwanted Options
		"-DZ3_BUILD_EXECUTABLE:BOOL=FALSE"
		"-DZ3_USE_LIB_GMP:BOOL=FALSE"
		"-DZ3_INCLUDE_GIT_DESCRIBE:BOOL=FALSE"
		"-DZ3_SAVE_CLANG_OPTIMIZATION_RECORDS:BOOL=FALSE"
		"-DZ3_ENABLE_TRACING_FOR_NON_DEBUG:BOOL=FALSE"
		"-DZ3_ENABLE_EXAMPLE_TARGETS:BOOL=FALSE"
		"-DZ3_ENABLE_CFI:BOOL=FALSE"
		"-DZ3_BUILD_DOCUMENTATION:BOOL=FALSE"
		"-DZ3_BUILD_TEST_EXECUTABLES:BOOL=FALSE"
		"-DZ3_BUILD_DOTNET_BINDINGS:BOOL=FALSE"
		"-DZ3_BUILD_JAVA_BINDINGS:BOOL=FALSE"
		"-DZ3_BUILD_PYTHON_BINDINGS:BOOL=FALSE"
)


# Define our shared library target to depend on the external z3 build
# That is, when this target is made, it makes the external z3 build first
add_dependencies("${Z3_LIB_TARGET}" "${Z3_BUILDER}")
