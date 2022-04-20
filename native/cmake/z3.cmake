# This file configures a make target for z3, which other targets can depend on
#
# The following variables should be defined before including this file:
#  Z3_ACQUISITION_MODE - The method used to acquire z3. Either SYSTEM, DOWNLOAD, PATH, or BUILD
#  Z3_MAKE_TARGET - The name of the z3 make target that buils the z3 library internal target
#  Z3_LIB_EXTENSION (Optional) - The extension used by shared libraries on this OS
#  Z3_FORCE_CLEAN (Optional) - If Z3 needs to be downloaded / built, this forces it to be fresh
# All variables required by the the selected mode, define in the respective cmake/z3/z3_<mode> file
# Except those that are defined in this file and thus do not need to be defined earlier
#
# This file defines the following variables as needed:
#  Z3_INCLUDE_DIR - The directory containing the headers linked targets may wish to include
#  Z3_LINK_TARGET - The Z3 target to link to
#  Z3_LIB         - The shared Z3 libary pointed to by the link target

include(fetch)

# Wrapping this in a function to create a new scope
function(_acquire_z3_helper)

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
	string(TOLOWER "${Z3_ACQUISITION_MODE}" LOW_ACQ)
	set( Z3_DIR "${CMAKE_BINARY_DIR}/z3/${LOW_ACQ}/" ) # Vary Z3 dir depending on mode
	set( Z3_LIB_NAME "libz3${Z3_LIB_EXTENSION}" )
	set( Z3_LIB "${Z3_DIR}/bin/${Z3_LIB_NAME}" )

	# Where Z3 headers are installed
	set( Z3_INCLUDE_DIR "${Z3_DIR}/include/" ) # Define for acquisition mode's usage
	set( Z3_INCLUDE_DIR "${Z3_INCLUDE_DIR}" PARENT_SCOPE ) # Parent scope, but not child scope
	message(STATUS "Using z3 include directory: ${Z3_INCLUDE_DIR}")

	#################################################
	#                   Z3 Target                   #
	#################################################

	# Add a z3 library target
	set(Z3_LINK_TARGET "${Z3_LIB_NAME}")
	set(Z3_LINK_TARGET "${Z3_LINK_TARGET}" PARENT_SCOPE)
	add_library( "${Z3_LINK_TARGET}"
		SHARED
		IMPORTED
		GLOBAL # Scopes the library outside of its directory
	)

	if(EXISTS "${Z3_LIB}" AND NOT "${Z3_FORCE_CLEAN}")
		message(STATUS "FORCE_CLEAN_Z3 is set to: ${FORCE_CLEAN_Z3}")
		message("Existing z3 library, prioritizing it over all else.")
	else()
		if(Z3_ACQUISITION_MODE STREQUAL DOWNLOAD)
			include(z3_download)
		elseif(Z3_ACQUISITION_MODE STREQUAL BUILD)
			include(z3_build)
		else()
			message(FATAL_ERROR "Unsupported z3 acquisition mode requested: ${Z3_ACQUISITION_MODE}")
		endif()
	endif()

	# Point the target to the shared library file
	message(STATUS "Configuring top level z3 target")
	set_property(TARGET "${Z3_LINK_TARGET}" PROPERTY
		IMPORTED_LOCATION "${Z3_LIB}"
	)

	# Expose a make target to allow `make z3` to acquire z3
	message(STATUS "Generating z3 make target: ${Z3_MAKE_TARGET}")
	add_custom_target("${Z3_MAKE_TARGET}"
		COMMENT "Acquiring z3"
		DEPENDS "${Z3_LINK_TARGET}"
	)

endfunction()

# Wrapping this in a function to create a new scope
function(_acquire_z3)

	# Get Z3 via system or path if requested
	message(STATUS "z3 acquisition mode set to: ${Z3_ACQUISITION_MODE}")
	list(APPEND CMAKE_MODULE_PATH "${CMAKE_CURRENT_SOURCE_DIR}/cmake/z3")
	if(Z3_ACQUISITION_MODE STREQUAL SYSTEM)
		include(z3_system)
	elseif(Z3_ACQUISITION_MODE STREQUAL PATH)
		include(z3_path)
	else()
		_acquire_z3_helper()
		return()
	endif()

	# Add a z3 library target
	set(Z3_LINK_TARGET "z3")
	set(Z3_LINK_TARGET "${Z3_LINK_TARGET}" PARENT_SCOPE)
	message(STATUS "Creating Z3 link target '${Z3_LINK_TARGET}' with lib: ${Z3_LIB}")
	add_library("${Z3_LINK_TARGET}" SHARED IMPORTED GLOBAL)
	set_property(TARGET "${Z3_LINK_TARGET}" PROPERTY IMPORTED_LOCATION "${Z3_LIB}")

endfunction()


_acquire_z3()