# This file configures a make target for z3, which other targets can depend on
#
# The following variables should be defined before including this file:
#  Z3_FORCE_REBUILD - If false, rebuilds will not occur if libz3 is present during configuration
#                     Note: It is reccomended you reconfigure cmake after a libz3 build otherwise
#                     libz3 may re-build every time make is invoked as it is using an old configuration
#  Z3_REPO_LINK     - The git repo to download Z3 source files from
#  Z3_GIT_COMMIT    - The git commit to download from Z3_REPO_LINK
#  Z3_NUM_CORES     - The number of cores used to compile z3 with (i.e. make -j<this>)
#  Z3_LIB           - The location of the z3 library once installed
#  Z3_DIR           - The directory the z3 install tree should be placed
#  Z3_LIB_PRIVATETARGET        - The name of the z3 library target
#  Z3_BUILD_RELEASE_MODE       - On to build in release mode; off for debug mode
#  Z3_LIB_EXTENSION (Optional) - The extension used by shared libraries on this OS

# Wrapping this in a function to create a new scope
function(_build_z3)

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
			set(SKIP_DOWNLOAD_IF_EXISTS "DOWNLOAD_COMMAND" "") # Unquoted is needed here
		else()
			message("No existing z3 directory found. A new fresh clone will be downloaded.")
		endif()

		# If we desire build parallelization
		if(Z3_NUM_CORES LESS 1)
			message(FATAL_ERROR
				"Z3 cannot be built with fewer than 1 core. "
				"To build, update the Z3_NUM_CORES variable."
			)
		elseif(Z3_NUM_CORES GREATER 1)

			# Parallelization args depend on the make generator
			# First we must locate the system's make program from a list of make
			# generators which support build parallelization
			find_program(MAKER NAMES gmake make)

			# If no such generator is found, we look for generators which do not
			if (MAKER MATCHES "-NOTFOUND$")
				find_program(MAKER NAMES nmake)

				# If no such option is found we error out
				if (MAKER MATCHES "-NOTFOUND$")
					message(FATAL_ERROR "No suitable make program found.")
				else()
					message(WARNING
						"Program ${MAKER} does not support build parallelization."
						" Building Z3 without build parallelization enabled."
					)
					set(BUILD_COMMAND "BUILD_COMMAND" "${MAKER}") # No args, nmake doesn't support -j
				endif()

			# If we find an acceptable generator, use it
			else()
				message(STATUS "Using ${Z3_NUM_CORES} cores to build Z3.")
				set(BUILD_COMMAND
					"BUILD_COMMAND"
					"${MAKER}"
					"-j${Z3_NUM_CORES}"
				)
			endif()
		endif()

		# Set build options
		if (Z3_BUILD_RELEASE_MODE)
			message(STATUS "Building z3 in Release mode")
			set(BUILDTYPE "Release")
			set(FLTO TRUE)
		else()
			message(WARNING "Building z3 in Debug mode")
			set(BUILDTYPE "Debug")
			set(FLTO FALSE)
		endif()
		# Define Z3 as an external project
		set( BUILDER "z3_build" )
		ExternalProject_Add("${BUILDER}"
			# Download options
			${SKIP_DOWNLOAD_IF_EXISTS} # This should *not* be quoted
			GIT_REPOSITORY "${Z3_REPO_LINK}"
			GIT_TAG "${Z3_GIT_COMMIT}"
			GIT_CONFIG "advice.detachedHead=false" # Silence unneeded warnings
			GIT_SHALLOW TRUE                       # We don't need a deep clone
			GIT_PROGRESS TRUE                      # Show progress while cloning
			# Where to put the z3 directory
			PREFIX "${Z3_DIR}"
			# Build options
			${BUILD_COMMAND} # This should *not* be quoted
			CMAKE_CACHE_ARGS
				"-DZ3_SINGLE_THREADED:BOOL=FALSE"
				"-DZ3_INCLUDE_GIT_HASH:BOOL=TRUE"
				# Build Options
				"-DCMAKE_BUILD_TYPE:STRING=${BUILDTYPE}"
				"-DZ3_LINK_TIME_OPTIMIZATION:BOOL=${FLTO}"
				"-DZ3_BUILD_LIBZ3_SHARED:BOOL=TRUE"
				"-DWARNINGS_AS_ERRORS:STRING=SERIOUS_ONLY"
				# Install Options
				"-DCMAKE_INSTALL_INCLUDEDIR:PATH=${Z3_INCLUDE_DIR}" # Absolute path
				"-DCMAKE_INSTALL_LIBDIR:PATH=${Z3_DIR}/bin/"        # Absolute path
				# This should never be used, but just in case:
				"-DCMAKE_INSTALL_PREFIX:PATH=${Z3_DIR}"
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
			# TODO BUILD_BYPRODUCTS for Ninja build system usage
		)

		# Define our shared library target to depend on the external z3 build
		# That is, when this target is made, it builds z3 first
		add_dependencies("${Z3_LIB_PRIVATE_TARGET}" "${BUILDER}")
	endif()

endfunction()

_build_z3()
