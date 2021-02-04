# cppcheck
if(CPP_CHECK)
	message(WARNING "cppcheck's internal AST can break because of control block initalizers."
			"Until this bug is fixed we cannot use cppcheck. Skipping.")
	set(CPP_CHECK OFF)
	# set(CPPCHECK_FLAGS "cppcheck"
	# 	"--enable=all"
	# 	"--std=c++17"
	# 	"--error-exitcode=1"
	# 	"--inline-suppr"
	# 	# TODO: remove this after python wrapper and c ABI made
	# 	"--suppress=unusedFunction"
	# 	# cppcheck might have path issues; this check is redundant since we can compile successfully
	# 	"--suppress=missingIncludeSystem"
	# 	# cppcheck is over-aggressive and includes static member variables, we do not want that
	# 	"--suppress=duplInheritedMember"
	# 	# cppcheck is over-aggressive and that leads to a ton of false positives
	# 	# The compilers and clang-tidy both have shadow detection enabled anyway so we disable this
	# 	"--suppress=shadowVariable"
	# 	# Allow the above suppression to be unmatched
	# 	# That is: do not mandate files violate the conditions that invoke the above suppressions
	# 	# Note: this does not apply to inline suppressions
	# 	"--suppress=unmatchedSuppression"
	# )
	# set(CMAKE_C_CPPCHECK ${CPPCHECK_FLAGS})
	# set(CMAKE_CXX_CPPCHECK ${CPPCHECK_FLAGS})
endif()

# Include What You Use
if(IWYU)
	if(APPLE)
		set(IWYU_PATH "include-what-you-use")
	else()
		set(IWYU_PATH "iwyu" "--cxx17ns")
	endif()
	set(CMAKE_C_INCLUDE_WHAT_YOU_USE "${IWYU_PATH}")
	set(CMAKE_CXX_INCLUDE_WHAT_YOU_USE "${IWYU_PATH}")
endif()

# Link What You Use
if(LWYU)
	if(APPLE)
		message(WARNING "Link what you use is not supported by Apple's linker. Skipping.")
		set(LWYU OFF)
	else()
		set(CMAKE_LINK_WHAT_YOU_USE TRUE)
	endif()
endif()

# Clang Tidy
if(CLANG_TIDY)
	if(APPLE)
		message(WARNING "Clang Tidy might not behave well with boost headers")
		set(CMAKE_C_CLANG_TIDY "/usr/local/opt/llvm/bin/clang-tidy")
		set(CMAKE_CXX_CLANG_TIDY "/usr/local/opt/llvm/bin/clang-tidy")
	else()
		set(CMAKE_C_CLANG_TIDY "clang-tidy-11")
		set(CMAKE_CXX_CLANG_TIDY "clang-tidy-11")
	endif()
endif()
