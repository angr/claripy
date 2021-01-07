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
# TODO: break apart
add_library("${SHARED_LIB_NAME}" SHARED
	# Expression
	./expression/cache_key.cpp
	./expression/private/factory_cache.cpp
		# RawTypes
		./expression/raw/type/fp.cpp
		./expression/raw/type/vs.cpp
		./expression/raw/type/bv.cpp
		./expression/raw/type/int.cpp
		./expression/raw/type/bool.cpp
		./expression/raw/type/base.cpp
		./expression/raw/type/bits.cpp
		./expression/raw/type/string.cpp
	# Utils
		./utils/error/claricpp.cpp
		# Log
			# Level
			./utils/log/level/ostream.cpp
			./utils/log/level/access.cpp
			# Style
			./utils/log/style/level_timestamp_message.cpp
			./utils/log/style/access.cpp
			# Backend
			./utils/log/backend/access.cpp
			./utils/log/backend/multiplex.cpp
			./utils/log/backend/ostream.cpp
			./utils/log/backend/clog.cpp
			./utils/log/backend/cerr.cpp
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

add_subdirectory(expression)

# Link additional libraries
# We do not want their functions exposed by our shared object so we designate them private
# target_link_libraries("${SHARED_LIB_NAME}"
# )

# Configure library compilation and linking
if(CMAKE_BUILD_TYPE MATCHES Release)
	set_property(TARGET "${SHARED_LIB_NAME}" PROPERTY INTERPROCEDURAL_OPTIMIZATION TRUE)
endif()
