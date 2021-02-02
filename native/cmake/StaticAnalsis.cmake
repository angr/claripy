# cppcheck
if(CPP_CHECK)
	if (APPLE)
		message(WARNING "cppcheck's internal AST can break because of control block initalizers on mac."
				"Until this bug is fixed we cannot use cppcheck on mac. Skipping.")
		set(CPP_CHECK OFF)
	else()
		set(CPPCHECK_FLAGS "cppcheck"
			"--enable=all"
			"--std=c++17"
			"--error-exitcode=1"
			"--inline-suppr"
		)
		set(CMAKE_C_CPPCHECK ${CPPCHECK_FLAGS})
		set(CMAKE_CXX_CPPCHECK ${CPPCHECK_FLAGS})
	endif()
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
