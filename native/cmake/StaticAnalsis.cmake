if(CPP_CHECK)
	set(CPPCHECK "cppcheck" "--std=c++17" "--error-exitcode=1" "--inline-suppr")
	set(CMAKE_C_CPPCHECK "${CPPCHECK}")
	set(CMAKE_CXX_CPPCHECK "${CPPCHECK}")
endif()
if(IWYU)
	if(APPLE)
		set(IWYU_PATH "include-what-you-use")
	else()
		set(IWYU_PATH "iwyu" "--cxx17ns")
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
	if(APPLE)
		message(WARNING "Clang Tidy might not behave well with boost headers")
		set(CMAKE_C_CLANG_TIDY "/usr/local/opt/llvm/bin/clang-tidy")
		set(CMAKE_CXX_CLANG_TIDY "/usr/local/opt/llvm/bin/clang-tidy")
	else()
		set(CMAKE_C_CLANG_TIDY "clang-tidy-11")
		set(CMAKE_CXX_CLANG_TIDY "clang-tidy-11")
	endif()
endif()
