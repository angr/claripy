add_library(${SS_SUPPORT_LIB} SHARED
	# AST
	./ast/bool.cpp
	./ast/base.cpp
	./ast/cache_key.cpp
	# Annotations
	./annotations/base.cpp
	./annotations/simplification_avoidance.cpp
	# Ops
	./ops/classifications.cpp
	./ops/operations.cpp
	# Simplifications
	./simplifications/manager.cpp
)
