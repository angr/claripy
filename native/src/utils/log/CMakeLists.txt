# Add current directory's source files
target_sources("${CLARICPP}" PRIVATE
	# Level
	level/ostream.cpp
	level/access.cpp
	# Style
	style/abstract_base.cpp
	style/level_timestamp_message.cpp
	style/access.cpp
	# Backend
	backend/abstract_base.cpp
	backend/access.cpp
	backend/multiplex.cpp
	backend/ostream.cpp
	backend/clog.cpp
	backend/cerr.cpp
)
