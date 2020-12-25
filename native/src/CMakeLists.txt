# Find required packages
# find_package(Boost 1.7 REQUIRED COMPONENTS
# )

# Include additional header files
# include_directories(${Boost_INCLUDE_DIRS})

# Create the shared object target
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
		# Log
		./utils/log/level_map.cpp
			# Style
			./utils/log/style/abstract_base.cpp
			./utils/log/style/level_timestamp_message.cpp
			./utils/log/style/access.cpp
			# Backend
			./utils/log/backend/abstract_base.cpp
			./utils/log/backend/access.cpp
	# Annotations
	./annotations/base.cpp
	./annotations/simplification_avoidance.cpp
	# Ops
	./ops/classifications.cpp
	./ops/operations.cpp
	# Simplifications
	./simplifications/private/op_map.cpp
	./simplifications/simplifiers.cpp
	./simplifications/simplify.cpp
	# Errors
	./errors/claricpp.cpp
)

# Link additional libraries
# We do not want their functions exposed by our shared object so we designate them private
# target_link_libraries("${SHARED_LIB_NAME}"
# )

# Configure library compilation and linking
if(CMAKE_BUILD_TYPE MATCHES Release)
	set_property(TARGET "${SHARED_LIB_NAME}" PROPERTY INTERPROCEDURAL_OPTIMIZATION TRUE)
endif()
