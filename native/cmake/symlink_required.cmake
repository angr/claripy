# Functions which are basically ln -sf

# Define a symlink function that FATAL_ERROR's on failure
function(symlink_required SRC DST)
	file(CREATE_LINK "${SRC}" "${DST}"
		RESULT RES
		SYMBOLIC
	)
	if (NOT "${RES}" STREQUAL "0")
		message(FATAL_ERROR
			"Symlink creation failed. Could not create the following symlink:"
			"\n\t${SRC} -> ${DST}"
			"\nRecieved error: ${RES}"
		)
	endif()
endfunction()

function(symlink_required_rm_old SRC DST)
	file(REMOVE_RECURSE "${DST}")
	symlink_required("${SRC}" "${DST}")
endfunction()
