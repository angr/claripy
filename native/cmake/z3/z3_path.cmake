# This file configures a make target for z3, which other targets can depend on
#
# The following variables should be defined before including this file:
#  Z3_INCLUDE_PATH - The path to the include directory (z3 header files) that will be sym-linked in
#  Z3_LIB_PATH     - The path to the z3 library that will be sym-linked in
#  Z3_LIB          - The location of the z3 library once installed
#  Z3_DIR          - The directory the z3 install tree should be placed


# Don't bother re-linking if it already works
if (EXISTS "${Z3_LIB}")
	message(STATUS "Existing z3 library linked, prioritizing it above all else.")
elseif (EXISTS "${Z3_DIR}/include/" OR EXISTS "${Z3_DIR}/bin/")
	message(STATUS
		"Directory ${Z3_DIR} is polluted."
		" Refusing to continue. Please clean it and try again"
	)
else()

	# Setup symlinks
	include(symlink_required)
	file(MAKE_DIRECTORY "${Z3_DIR}/bin/")
	symlink_required("${Z3_LIB_PATH}" "${Z3_LIB}")
	symlink_required("${Z3_INCLUDE_PATH}" "${Z3_DIR}/include")

endif()
