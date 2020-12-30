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
	# AST
	./ast/cache_key.cpp
	./ast/private/factory_cache.cpp
		# RawTypes
		./ast/raw_types/fp.cpp
		./ast/raw_types/vs.cpp
		./ast/raw_types/bv.cpp
		./ast/raw_types/int.cpp
		./ast/raw_types/bool.cpp
		./ast/raw_types/base.cpp
		./ast/raw_types/bits.cpp
		./ast/raw_types/string.cpp
	# Utils
		./utils/errors/claricpp.cpp
		# Log
			# Level
			./utils/log/level/ostream.cpp
			./utils/log/level/access.cpp
			# Style
			./utils/log/styles/level_timestamp_message.cpp
			./utils/log/styles/access.cpp
			# Backend
			./utils/log/backends/access.cpp
			./utils/log/backends/ostream.cpp
			./utils/log/backends/clog.cpp
	# Annotations
	./annotations/base.cpp
	./annotations/simplification_avoidance.cpp
	# Ops
	./ops/classifications.cpp
	# Interface
	./interface/base.cpp
	./interface/op/op.cpp
	# Simplification
	./simplification/private/op_map.cpp
	./simplification/simplifiers.cpp
	./simplification/simplify.cpp
)

# Link additional libraries
# We do not want their functions exposed by our shared object so we designate them private
# target_link_libraries("${SHARED_LIB_NAME}"
# )

# Configure library compilation and linking
if(CMAKE_BUILD_TYPE MATCHES Release)
	set_property(TARGET "${SHARED_LIB_NAME}" PROPERTY INTERPROCEDURAL_OPTIMIZATION TRUE)
endif()
