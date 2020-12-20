add_library("${SHARED_LIB_NAME}" SHARED
	# AST
	./ast/raw_types/fp.cpp
	./ast/raw_types/vs.cpp
	./ast/raw_types/bv.cpp
	./ast/raw_types/int.cpp
	./ast/raw_types/bool.cpp
	./ast/raw_types/base.cpp
	./ast/raw_types/bits.cpp
	./ast/raw_types/string.cpp
	./ast/cache_key.cpp
	./ast/factory.cpp
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
set_target_properties("${SHARED_LIB_NAME}" PROPERTIES
            CXX_STANDARD 17
)
