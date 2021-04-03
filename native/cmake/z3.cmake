# This file configures a make target for z3, which other targets can depend on

# Add extra cmake files to path
list(APPEND CMAKE_MODULE_PATH "${CMAKE_CURRENT_SOURCE_DIR}/cmake/z3")

# Execute the relevant cmake file
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
