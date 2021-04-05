# This file configures a make target for z3, which other targets can depend on
#
# The following variables should be defined before including this file:
#  Z3_ACQUISITION_MODE - The method used to acquire z3. Either SYSTEM, DOWNLOAD, PATH, or BUILD
# All variables required by the the selected mode, define in the respective cmake/z3/z3_<mode> file
#
# This file defines the following variables:
#  Z3_LIB_TARGET - The name of the z3 target
#  Z3_INCLUDE_DIR - The directory containing the headers linked targets may wish to include

# Wrapping this in a function to create a new scope
function(_acquire_z3)

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
	set( Z3_DIR "${CMAKE_BINARY_DIR}/z3/${Z3_ACQUISITION_MODE}/" ) # Vary Z3 dir depending on mode
	set( Z3_LIB_NAME "libz3${Z3_LIB_EXTENSION}" )
	set( Z3_LIB "${Z3_DIR}/bin/${Z3_LIB_NAME}" )

	### Constants defined for use outside of this file ###

	# The Z3 library target
	set( Z3_LIB_TARGET "z3" ) # Child scope
	set( Z3_LIB_TARGET "${Z3_LIB_TARGET}" PARENT_SCOPE ) # Parent scope, but not child scope

	# Where Z3 headers are installed
	set( Z3_INCLUDE_DIR "${Z3_DIR}/include/" PARENT_SCOPE ) # Parent scope, but not child scope

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

	# Add extra cmake files to the include path
	list(APPEND CMAKE_MODULE_PATH "${CMAKE_CURRENT_SOURCE_DIR}/cmake/z3")

	# Acquire Z3
	if(Z3_ACQUISITION_MODE STREQUAL SYSTEM)
		include(z3_system)
	elseif(Z3_ACQUISITION_MODE STREQUAL DOWNLOAD)
		include(z3_download)
	elseif(Z3_ACQUISITION_MODE STREQUAL PATH)
		include(z3_path)
	elseif(Z3_ACQUISITION_MODE STREQUAL BUILD)
		include(z3_build)
	else()
		message(FATAL_ERROR "Unsupported z3 acquisition mode requested: ${Z3_ACQUISITION_MODE}")
	endif()

	# Point the target to the shared library file
	set_property(TARGET "${Z3_LIB_TARGET}" PROPERTY
		IMPORTED_LOCATION "${Z3_LIB}"
	)

endfunction()

_acquire_z3()
