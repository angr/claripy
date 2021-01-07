# Add current directory's source files
target_sources("${SHARED_LIB_NAME}" PRIVATE
	# Level
	level/ostream.cpp
	level/access.cpp
	# Style
	style/level_timestamp_message.cpp
	style/access.cpp
	# Backend
	backend/access.cpp
	backend/multiplex.cpp
	backend/ostream.cpp
	backend/clog.cpp
	backend/cerr.cpp
)
