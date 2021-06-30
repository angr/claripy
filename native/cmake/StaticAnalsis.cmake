# cppcheck
if(CPP_CHECK)
	message(WARNING "cppcheck's internal AST can break because of control block initalizers."
			"Until this bug is fixed cppcheck may not pass.")
	find_program(CPP_CHECK_PATH "cpp-check" REQUIRED)
	set(CPPCHECK_CMD "${CPP_CHECK_PATH}"
		"--enable=all"
		"--std=c++17"
		"--error-exitcode=1"
		"--inline-suppr"
		# TODO: remove this after python wrapper and c ABI made
		"--suppress=unusedFunction"
		# cppcheck might have path issues; this check is redundant since we can compile successfully
		"--suppress=missingIncludeSystem"
		# cppcheck is over-aggressive and includes static member variables, we do not want that
		"--suppress=duplInheritedMember"
		# cppcheck is over-aggressive and that leads to a ton of false positives
		# The compilers and clang-tidy both have shadow detection enabled anyway so we disable this
		"--suppress=shadowVariable"
		# Allow the above suppression to be unmatched
		# That is: do not mandate files violate the conditions that invoke the above suppressions
		# Note: this does not apply to inline suppressions
		"--suppress=unmatchedSuppression"
	)
	set(CMAKE_C_CPPCHECK ${CPPCHECK_CMD})
	set(CMAKE_CXX_CPPCHECK ${CPPCHECK_CMD})
endif()

# Include What You Use
if(IWYU)
	if(APPLE)
		find_program(IWYU_PATH "include-what-you-use" "iwyu" REQUIRED)
	else()
		find_program(IWYU_PATH "iwyu" "include-what-you-use" REQUIRED)
		set(IWYU_PATH "${IWYU_PATH}" "--cxx17ns")
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
	set(CLANG_TIDY_NAMES "clang-tidy-11" "clang-tidy")
	message(WARNING "Clang Tidy might not behave well with boost headers")
	if(APPLE)
		find_program(CLANG_TIDY_PATH ${CLANG_TIDY_NAMES}
			HINTS "/usr/local/opt/llvm/bin/"
			REQUIRED
		)
	else()
		find_program(CLANG_TIDY_PATH ${CLANG_TIDY_NAMES} REQUIRED)
	endif()
	set(CMAKE_C_CLANG_TIDY "${CLANG_TIDY_PATH}")
	set(CMAKE_CXX_CLANG_TIDY "${CLANG_TIDY_PATH}")
endif()
