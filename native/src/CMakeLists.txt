# Find required packages
# find_package(Boost 1.7 REQUIRED COMPONENTS
# )

# Include additional header files
# include_directories(${Boost_INCLUDE_DIRS})


#################################################
#                                               #
#                Static Analysis                #
#                                               #
#################################################


if(CPP_CHECK)
	set(CMAKE_C_CPPCHECK "cppcheck")
	set(CMAKE_CXX_CPPCHECK "cppcheck")
endif()
if(IWYU)
	if(APPLE)
		set(IWYU_PATH "include-what-you-use")
	else()
		set(IWYU_PATH "iwyu")
	endif()
	set(CMAKE_C_INCLUDE_WHAT_YOU_USE "${IWYU_PATH}")
	set(CMAKE_CXX_INCLUDE_WHAT_YOU_USE "${IWYU_PATH}")
endif()
if(LWYU)
	if(APPLE)
		message(WARNING "Link what you use is not supported by Apple's linker. Skipping.")
	else()
		set(CMAKE_LINK_WHAT_YOU_USE TRUE)
	endif()
endif()
if(CLANG_TIDY)
	set(CMAKE_C_CLANG_TIDY "clang-tidy" "-checks=*,readability=*,boost=*,clang-analyzer=*")
endif()


#################################################
#                                               #
#             Create Library Target             #
#                                               #
#################################################


# Create the shared object target
add_library("${SHARED_LIB_NAME}" SHARED
	# Annotation
	./annotation/base.cpp
	./annotation/simplification_avoidance.cpp
	# Op
	./op/classifications.cpp
	# Simplification
	# TODO
	# ./simplification/private/op_map.cpp
	# ./simplification/simplifiers.cpp
	# ./simplification/simplify.cpp
)

# Add sub directories
add_subdirectory(utils)
add_subdirectory(expression)

# Link additional libraries
# We do not want their functions exposed by our shared object so we designate them private
# target_link_libraries("${SHARED_LIB_NAME}"
# )

# Configure library compilation and linking
if(CMAKE_BUILD_TYPE MATCHES Release)
	set_property(TARGET "${SHARED_LIB_NAME}" PROPERTY INTERPROCEDURAL_OPTIMIZATION TRUE)
endif()
