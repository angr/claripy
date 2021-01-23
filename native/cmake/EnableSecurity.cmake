# This file enables a bunch of security flags

# Check compatability
if(ENABLE_MEMCHECK)
	message(FATAL_ERROR "ENABLE_SECURITY and ENABLE_MEMCHECK are mutually exclusive")
elseif(CLANG_TIDY AND CMAKE_CXX_COMPILER_ID STREQUAL "GNU")
	message(FATAL_ERROR
		"ENABLE_SECURITY and CLANG_TIDY are mutually exclusive when not using clang."
		"\nWhen compiling with gcc we add gcc specific compile-flags that clang tidy cannot handle."
	)
endif()

# Macros that have never been defined before
target_compile_definitions("${CLARICPP}" PRIVATE "_GLIBCXX_ASSERTIONS")

# Basic Security flags
target_compile_options("${CLARICPP}" PRIVATE
	"-U_FORTIFY_SOURCE"   # Undefine compiler built-in fortification default
	"-D_FORTIFY_SOURCE=2" # Update fortify source to level 2
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

# GCC only
if(CMAKE_CXX_COMPILER_ID STREQUAL "GNU")
	target_compile_options("${CLARICPP}" PRIVATE
		"-fstack-clash-protection" # Exists in newer versions of llvm
	)
endif()

# Hardware security
if (ENABLE_CET)
	target_compile_options("${CLARICPP}" PRIVATE "-fcf-protection=full")
elseif(CMAKE_CXX_COMPILER_ID STREQUAL "GNU")
	target_compile_options("${CLARICPP}" PRIVATE
		"-mindirect-branch=thunk"
		"-mfunction-return=thunk"
		"-fcf-protection=none" # Disable CET
	)
endif()

# Non-Apple Linker flags
if(NOT CMAKE_CXX_COMPILER_ID STREQUAL "AppleClang") # Apple Clang doesn't like these
	target_link_options("${CLARICPP}" PRIVATE
		"LINKER:-z,relro,-z,now"
		"LINKER:-z,noexecstack"
		"LINKER:-dynamicbase" # Just in case
	)
else()
	message(WARNING "AppleClang does not support important security based linker flags")
endif()

# Linker Flags
target_link_options("${CLARICPP}" PRIVATE
	"-fsanitize=address" # Link relevant sanitization functions
	"-O2" # Enable source hardening, avoid the dangers of O3
)
