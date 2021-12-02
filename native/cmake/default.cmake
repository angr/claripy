# default(x value) = if not defined(x): set(x value)

function(default VARI VAL)
	if (NOT DEFINED "${VARI}")
		set("${VARI}" "${VAL}" PARENT_SCOPE)
	else()
		message(STATUS "Overriding ${VARI} with value: ${${VARI}}")
	endif()
endfunction()
