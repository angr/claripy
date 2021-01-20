#################################################
#                                               #
#                Static Analysis                #
#                                               #
#################################################


if(CPP_CHECK)
	set(CMAKE_C_CPPCHECK "cppcheck" "--error-exitcode=1" "--inline-suppr")
	set(CMAKE_CXX_CPPCHECK "cppcheck" "--error-exitcode=1" "--inline-suppr")
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
	set(CMAKE_C_CLANG_TIDY "clang-tidy-11"
		            "-checks=-*,readability-*,boost-*,clang-analyzer-*,-readability-named-parameter,-readability-redundant-member-init,-readability-else-after-return"
		"-warnings-as-errors=-*,readability-*,boost-*,clang-analyzer-*"
	)
	set(CMAKE_CXX_CLANG_TIDY "${CMAKE_C_CLANG_TIDY}")
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
	./simplification/private/op_map.cpp
	./simplification/simplifiers.cpp
	./simplification/simplify.cpp
)

# Add sub directories
add_subdirectory(utils)
add_subdirectory(expression)

# Configure library compilation and linking
if(CMAKE_BUILD_TYPE MATCHES Release)
	set_property(TARGET "${SHARED_LIB_NAME}" PROPERTY INTERPROCEDURAL_OPTIMIZATION TRUE)
endif()
