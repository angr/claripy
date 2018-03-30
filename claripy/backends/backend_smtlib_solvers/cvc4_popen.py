import subprocess
import logging

import re
from . import SMTLibSolverBackend, PopenSolverProxy

log = logging.getLogger(__name__)

def get_version():
    try:
        version_string = subprocess.check_output(['cvc4', '--version'])
        version_match = re.match('This is CVC4 version (.*)\n', version_string)

        if not version_match:
            return False, None, "Found malformed version string: {}".format(version_string)

        return True, version_match.group(1), None

    except subprocess.CalledProcessError as ex:
        return False, None, "Not found, error: {}".format(ex)
    except OSError as ex:
        return False, None, "Not found, error: {}".format(ex)


IS_INSTALLED, VERSION, ERROR = get_version()

if IS_INSTALLED:
    class CVC4Proxy(PopenSolverProxy):
        def __init__(self):
            p = subprocess.Popen(['cvc4', '--lang=smt', '-q', '--strings-exp'], stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            super(CVC4Proxy, self).__init__(p)


    class SolverBackendCVC4(SMTLibSolverBackend):
        def solver(self, timeout=None):
            """
            This function should return an instance of whatever object handles
            solving for this backend. For example, in Z3, this would be z3.Solver().
            """
            return CVC4Proxy()

    from ... import backend_manager as backend_manager
    backend_manager.backends._register_backend(SolverBackendCVC4(), 'smtlib_cvc4', False, False)

else:
    # CVC4 is not installed
    log.debug('CVC4 not found, corresponding SMTLib backend was disabled! Reason: {}'.format(ERROR))
    pass
