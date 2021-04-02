# This file configures a make target for z3, which other targets can depend on
# Relevant epoxrted variables:
#
#  Z3_LIB_TARGET - The name of the z3 target
#  Z3_INCLUDE_DIR - The directory containing the headers linked targets may wish to include

#################################################
#               Set by developer                #
#################################################

# Define the location of the z3 directory
set( Z3_DIR "${CMAKE_SRC_DIR}/z3/" )

# The name of the built shared object
# Note: This depends on the repo being built
set( Z3_LIB_SO_NAME "z3.so" )

# The link to the Z3 repo / commit
# If a local z3 directory exists it will be prefferred to this
set( Z3_REPO_LINK "https://github.com/Z3Prover/z3" )
set( Z3_REPO_LINK "${Z3_REPO_LINK}/tree/517d907567f4283ad8b48ff9c2a3f6dce838569e" )

#################################################
#                 Configuration                 #
#################################################

# Define various z3 sub-directories
set( Z3_BUILD_DIR "${Z3_DIR}/build/" )
set( Z3_INSTALL_DIR "${Z3_BUILD_DIR}/install/" )
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

# Define Z3 as an external project
set( Z3_BUILDER "z3_build" )
ExternalProject_Add("${Z3_BUILDER}"
	URL "${Z3_DIR}" "${Z3_REPO_LINK}" # Prefer local copy to URL
	PREFIX "${Z3_DIR}"                # Where to put the z3 directory
	BINARY_DIR "${Z3_BUILD_DIR}"      # Build directory
	CMAKE_CACHE_ARGS                  # Args for the z3 cmake
		"-DZ3_SINGLE_THREADED=FALSE"
		"-DZ3_INCLUDE_GIT_HASH=TRUE"
		"-DZ3_BUILD_PYTHON_BINDINGS=TRUE"
		# Build Options
		"-DCMAKE_BUILD_TYPE=Release"
		"-DZ3_BUILD_EXECUTABLE=FALSE"
		"-DZ3_BUILD_LIBZ3_SHARED=TRUE"
		"-DZ3_LINK_TIME_OPTIMIZATION=TRUE"
		"-DWARNINGS_AS_ERRORS=SERIOUS_ONLY"
		# Install Options
		"-DCMAKE_INSTALL_PREFIX=${Z3_INSTALL_DIR}" # This *should* never be used, but just in case
		"-DCMAKE_INSTALL_INCLUDEDIR=${Z3_INCLUDE_DIR}" # Absolute path
		"-DCMAKE_INSTALL_LIBDIR=${Z3_LIB_DIR}"         # Absolute path
		# Disable Unwanted Options
		"-DZ3_USE_LIB_GMP=FALSE"
		"-DZ3_INCLUDE_GIT_DESCRIBE=FALSE"
		"-DZ3_SAVE_CLANG_OPTIMIZATION_RECORDS=FALSE"
		"-DZ3_ENABLE_TRACING_FOR_NON_DEBUG=FALSE"
		"-DZ3_ENABLE_EXAMPLE_TARGETS=FALSE"
		"-DZ3_ENABLE_CFI=FALSE"
		"-DZ3_BUILD_DOCUMENTATION=FALSE"
		"-DZ3_BUILD_TEST_EXECUTABLES=FALSE"
		"-DZ3_BUILD_DOTNET_BINDINGS=FALSE"
		"-DZ3_BUILD_JAVA_BINDINGS=FALSE"
)

# Define our shared library target to depend on the external z3 build
# That is, when this target is made, it makes the external z3 build first
add_dependencies("${Z3_LIB_TARGET}" "${Z3_BUILDER}")
