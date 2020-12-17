add_library(${SS_SUPPORT_LIB} SHARED
	# AST
	./ast/fp.cpp
	./ast/vs.cpp
	./ast/bv.cpp
	./ast/int.cpp
	./ast/bool.cpp
	./ast/base.cpp
	./ast/bits.cpp
	./ast/string.cpp
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
