add_library(${SS_SUPPORT_LIB} SHARED
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
	# Annotations
	./annotations/base.cpp
	./annotations/simplification_avoidance.cpp
	# Ops
	./ops/classifications.cpp
	./ops/operations.cpp
	# Simplifications
	./simplifications/private.cpp
	./simplifications/simplifiers.cpp
	# Errors
	./errors/claricpp.cpp
)
