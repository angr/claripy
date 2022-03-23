# This file configures a make target for z3, which other targets can depend on
#
# The following variables should be defined before including this file:
#  Z3_INCLUDE_DIR - The path to the include directory (z3 header files) that will be sym-linked in


find_library(Z3_LIB z3 REQUIRED)
message("Found Z3 library: ${Z3_LIB}")
if(NOT EXISTS "${Z3_INCLUDE_DIR}")
	message(FATAL_ERROR "Cannot find: ${Z3_INCLUDE_DIR}")
endif()
