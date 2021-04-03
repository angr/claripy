# This file configures a make target for z3, which other targets can depend on
#
# The following variables should be defined before including this file:
#  Z3_FORCE_REBUILD (Required) - If false, rebuilds will not occur if libz3 is present during configuration
#                                Note: It is reccomended you reconfigure cmake after a libz3 build otherwise
#                                libz3 may re-build every time make is invoked as it is using an old configuration
#  Z3_NUM_CORES     (Required) - The number of cores used to compile z3 with (i.e. make -j<this>)
#  Z3_LIB_EXTENSION (Optional) - The extension used by shared libraries on this OS
#
# This file defines the following variables:
#  Z3_LIB_TARGET - The name of the z3 target
#  Z3_INCLUDE_DIR - The directory containing the headers linked targets may wish to include


#################################################
#               Set by developer                #
#################################################


# The link to the Z3 repo / commit
# If a local z3 directory exists it will be prefferred to this
set( Z3_REPO_LINK "https://github.com/Z3Prover/z3" )
set( Z3_GIT_COMMIT "517d907567f4283ad8b48ff9c2a3f6dce838569e" )

# Define the location of the z3 directory
set( Z3_DIR "${CMAKE_SOURCE_DIR}/z3/" )


#################################################
#               Program Constants               #
#################################################


# Determine the library's name
if (NOT DEFINED Z3_LIB_EXTENSION)
	if ("${CMAKE_SYSTEM_NAME}" STREQUAL "Linux")
		set( Z3_LIB_EXTENSION ".so" )
	elseif ("${CMAKE_SYSTEM_NAME}" STREQUAL "Darwin")
		set( Z3_LIB_EXTENSION ".dylib" )
	elseif ("${CMAKE_SYSTEM_NAME}" STREQUAL "Windows")
		set( Z3_LIB_EXTENSION ".dll" )
	else()
		message( FATAL_ERROR "Unknown operating system. Please manually set Z3_LIB_EXTENSION" )
	endif()
endif()

# Define various z3 sub-directories
set( Z3_INSTALL_DIR "${Z3_DIR}/install/" )
set( Z3_LIB_DIR "${Z3_INSTALL_DIR}/lib/" )
set( Z3_LIB "${Z3_LIB_DIR}/libz3${Z3_LIB_EXTENSION}" )

# Constants by name outside of this file:

# The Z3 library target
set( Z3_LIB_TARGET "z3" )

# Where Z3 headers are installed
set( Z3_INCLUDE_DIR "${Z3_INSTALL_DIR}/include/")


#################################################
#                   Z3 Target                   #
#################################################


# Add a z3 library target
# This allows us to make using z3 dependent on build later, if needed
add_library( "${Z3_LIB_TARGET}"
	SHARED
	IMPORTED
	GLOBAL # Scopes the library outside of its directory
)
# Point the target to the shared library file
set_property(TARGET "${Z3_LIB_TARGET}" PROPERTY
	IMPORTED_LOCATION "${Z3_LIB}"
)


#################################################
#              Build Configuration              #
#################################################


# This step is only necessary if the build does not already exist
if(EXISTS "${Z3_LIB}" AND NOT "${Z3_FORCE_REBUILD}")
	message("Found ${Z3_LIB}. Using it instead of rebuilding.")
else()
	message(WARNING
		"The next make invocation will build Z3."
		" If you intend to run make multiple times it is advised to re-run cmake first."
		" Failure to do so will result in Z3 being partially re-built during each make"
		" invoacation as the Z3 build-system regenerates files which triggers a rebuild."
	)

	# Dependencies
	include(ExternalProject)

	# If a local z3 dir exists, override download command with an empty string
	if(EXISTS "${Z3_DIR}")
		message("Existing z3 directory found. Prioritizing it over a fresh clone.")
		set(Z3_SKIP_DOWNLOAD_IF_EXISTS "DOWNLOAD_COMMAND" "") # Unquoted is needed here
	else()
		message("No existing z3 directory found. Cloning a new one.")
	endif()

	# If we desire build parallelization
	if (Z3_NUM_CORES GREATER 1)

		# Parallelization args depend on the make generator
		# First we must locate the system's make program from a list of make
		# generators which support build parallelization
		find_program(Z3_MAKE_EXE NAMES gmake make)

		# If no such generator is found, we look for generators which do not
		if (Z3_MAKE_EXE MATCHES "-NOTFOUND$")
			find_program(MAKE_EXE NAMES nmake)

			# If no such option is found we error out
			if (Z3_MAKE_EXE MATCHES "-NOTFOUND$")
				message(FATAL_ERROR "No suitable make program found.")
			else()
				message(WARNING
					"Program ${Z3_MAKE_EXE} does not support build parallelization."
					" Building Z3 without build parallelization enabled."
				)
				set(Z3_BUILD_COMMAND "BUILD_COMMAND" "${Z3_MAKE_EXE}") # No args, nmake doesn't support -j
			endif()

		# If we find an acceptable generator, use it
		else()
			message(STATUS "Using ${Z3_NUM_CORES} cores to build Z3.")
			set(Z3_BUILD_COMMAND
				"BUILD_COMMAND"
				"${Z3_MAKE_EXE}"
				"-j${Z3_NUM_CORES}"
			)
		endif()

	# Usage check
	elseif(Z3_NUM_CORES LESS 1)
		message(FATAL_ERROR
			"Z3 cannot be built with fewer than 1 core. "
			"To build, update the Z3_NUM_CORES variable."
		)
	endif()
	# Define Z3 as an external project
	set( Z3_BUILDER "z3_build" )
	ExternalProject_Add("${Z3_BUILDER}"
		# Download options
		${Z3_SKIP_DOWNLOAD_IF_EXISTS} # This should *not* be quoted
		GIT_REPOSITORY "${Z3_REPO_LINK}"
		GIT_TAG "${Z3_GIT_COMMIT}"
		GIT_CONFIG "advice.detachedHead=false" # Silence unneeded warnings
		GIT_SHALLOW TRUE                       # We don't need a deep clone
		GIT_PROGRESS TRUE                      # Show progress while cloning
		# Where to put the z3 directory
		PREFIX "${Z3_DIR}"
		# Build options
		${Z3_BUILD_COMMAND} # This should *not* be quoted
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
	# That is, when this target is made, it builds z3 first
	add_dependencies("${Z3_LIB_TARGET}" "${Z3_BUILDER}")
endif()
