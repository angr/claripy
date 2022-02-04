# This file configures Backward
#
# This file defines BACKWARD_ENABLED

message(STATUS "Configuring Backward...")

# Config
set(BACKWARD_DIR "${CMAKE_CURRENT_SOURCE_DIR}/backward-cpp/")
option(WARN_BACKWARD_LIMITATIONS "Warn about any limitations due to missing dependencies" ON)

# Error checking
if (NOT EXISTS "${BACKWARD_DIR}")
	message( FATAL_ERROR "${BACKWARD_DIR} does not exist, maybe use 'git submodule update --init'?")
endif()
if (NOT IS_DIRECTORY "${BACKWARD_DIR}")
	message( FATAL_ERROR "${BACKWARD_DIR} is not a directory; maybe delete it then use 'git submodule update --init'?")
endif()

# Include
list(APPEND CMAKE_MODULE_PATH "${BACKWARD_DIR}")
include(BackwardConfig)
list(REMOVE_ITEM CMAKE_MODULE_PATH "${BACKWARD_DIR}")

# Info
if (LIBDW_FOUND OR LIBBFD_FOUND OR LIBDWARF_FOUND)
	set(BACKWARD_BACKEND_ENABLED TRUE)
	if (LIBDW_FOUND)
		message(STATUS "Backward backend library: DW")
	elseif (LIBBFD_FOUND)
		message(STATUS "Backward backend library: BFD")
	elseif (LIBDWARF_FOUND)
		message(STATUS "Backward backend library: Dwarf")
	endif()
else()
	set(BACKWARD_BACKEND_ENABLED FALSE)
	if ("${REQUIRE_BACKWARD_BACKEND}")
		message(FATAL_ERROR "Backward backend could not be found")
	endif()
	if ("${WARN_BACKWARD_LIMITATIONS}")
		message(WARNING "Backward backend not library found; backtraces will be limited.")
	else()
		message("Backward backend not library found; backtraces will be limited.")
	endif()
endif()

message(STATUS "Backward config complete")
