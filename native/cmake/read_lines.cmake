# Read a file into RET_NAME as a list of strings
# file(STRINGS) but can handle ';' in the file

# A helper function which splits data into lines
function(split_into_lines DATA RET_NAME)
    string(REPLACE ";" "\\;" DATA "${DATA}") # Escape ;
    set(DATA "${DATA}\n") # Ensures the last element is grabbed
    set(RET "")

    # Loop through each line; and append them to RET
    string(FIND "${DATA}" "\n" INDEX)
    while(NOT INDEX STREQUAL -1)
        string(SUBSTRING "${DATA}" 0 "${INDEX}" NEXT)
        set(RET "${RET};${NEXT}") # list(APPEND) fails with ""
        # Find next new line
        math(EXPR INDEX "${INDEX}+1")
        string(SUBSTRING "${DATA}" "${INDEX}" -1 DATA) # Remove top line from DATA
        string(FIND "${DATA}" "\n" INDEX)
    endwhile()

    # Return each line (strip leading ;)
    string(SUBSTRING "${RET}" 1 -1 RET)
    set("${RET_NAME}" "${RET}" PARENT_SCOPE)
endfunction()

# file(STRINGS) except it can handle semicolons in files
function(read_lines FNAME RET_NAME)
    file(READ "${FNAME}" DATA)
    split_into_lines("${DATA}" RET)
    set("${RET_NAME}" "${RET}" PARENT_SCOPE) # Return
endfunction()