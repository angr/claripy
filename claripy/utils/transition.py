# pylint: disable=unused-import,unused-argument,exec-used
import sys

PY2 = str is bytes

def raise_from(new_error, old_error):
    if PY2:
        exec('raise type(new_error), new_error, sys.exc_info()[2]')
    else:
        exec('raise new_error from old_error')
