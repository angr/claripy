add_library(${SS_SUPPORT_LIB} SHARED
	# AST
	./ast/bv.cpp
	./ast/bool.cpp
	./ast/base.cpp
	./ast/bits.cpp
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
	./errors/errors.cpp
)
