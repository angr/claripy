# This file enables a bunch of security flags

function(enable_security TARGET ENABLE_MEMCHECK ENABLE_CET)
	# Check compatability
	if(ENABLE_MEMCHECK)
		message(FATAL_ERROR "ENABLE_SECURITY and ENABLE_MEMCHECK are mutually exclusive")
	elseif(CLANG_TIDY AND CMAKE_CXX_COMPILER_ID STREQUAL "GNU")
		message(FATAL_ERROR
			"ENABLE_SECURITY and CLANG_TIDY are mutually exclusive when not using clang."
			"\nWhen compiling with gcc we add gcc specific compile-flags that clang tidy cannot handle."
		)
	endif()

	# Macros
	target_compile_definitions("${TARGET}" PRIVATE "_GLIBCXX_ASSERTIONS")

	# Compiler flags
	target_compile_options("${TARGET}" PRIVATE
		"-U_FORTIFY_SOURCE"   # Undefine compiler built-in fortification default
		"-D_FORTIFY_SOURCE=2" # Update fortify source to level 2
		"-Wformat-nonliteral"
		"-m64"
		# "-mmitigate-rop" # Deprecated
		"-fsanitize=address"
		"-fstack-protector-all"
		"-Wstack-protector"
		"--param" "ssp-buffer-size=4"
		"-Wformat"
		"-Wformat-security"
		"-fpic"
		"-ftrapv"
		"-O2" # Enable source hardening, avoid the dangers of O3
		# "-fvtable-verify=std" # Requires custom gcc compilation with this flag enabled.
	)
	if(CMAKE_CXX_COMPILER_ID STREQUAL "GNU")
		# TODO: This exists in newer versions of llvm(?)
		target_compile_options("${TARGET}" PRIVATE "-fstack-clash-protection")
	endif()
	if (ENABLE_CET)
		target_compile_options("${TARGET}" PRIVATE "-fcf-protection=full")
	elseif(CMAKE_CXX_COMPILER_ID STREQUAL "GNU")
		target_compile_options("${TARGET}" PRIVATE
			"-mindirect-branch=thunk"
			"-mfunction-return=thunk"
			"-fcf-protection=none" # Disable CET
		)
	endif()

	# Linker flags
	target_link_options("${TARGET}" PRIVATE
		"-fsanitize=address" # Link relevant sanitization functions
		"-O2" # Enable source hardening, avoid the dangers of O3
	)
	if(NOT CMAKE_CXX_COMPILER_ID STREQUAL "AppleClang") # Apple Clang doesn't like these
		target_link_options("${TARGET}" PRIVATE
			"LINKER:-z,relro,-z,now"
			"LINKER:-z,noexecstack"
			"LINKER:-dynamicbase" # Just in case
		)
	else()
		message(WARNING "AppleClang does not support important security based linker flags")
	endif()
endfunction()