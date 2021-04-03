# This file configures a make target for z3, which other targets can depend on
#
# The following variables should be defined before including this file:
#  Z3_FORCE_REBUILD (Required) - If false, rebuilds will not occur if libz3 is present during configuration
#                                Note: It is reccomended you reconfigure cmake after a libz3 build otherwise
#                                libz3 may re-build every time make is invoked as it is using an old configuration
#  Z3_NUM_CORES     (Required) - The number of cores used to compile z3 with (i.e. make -j<this>)
#  Z3_LIB_EXTENSION (Optional) - The extension used by shared libraries on this OS
#
#  Z3_LIB_TARGET - The name of the z3 target
#  Z3_INCLUDE_DIR - The directory containing the headers linked targets may wish to include
#

message(FATAL_ERROR "Z3 System Not Implemented")
