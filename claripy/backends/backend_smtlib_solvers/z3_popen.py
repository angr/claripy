import subprocess
import logging

import re
from claripy.backends.backend_smtlib_solvers import SMTLibSolverBackend, PopenSolverProxy

log = logging.getLogger(__name__)

def get_version():
    try:
        version_string = subprocess.check_output(['z3', '-version'])
        version_match = re.match('Z3 version (.*)\n', version_string)

        if not version_match:
            return False, None, "Found malformed version string: {}".format(version_string)

        return True, version_match.group(1), None

    except subprocess.CalledProcessError as ex:
        return False, None, "Not found, error: {}".format(ex)
    except OSError as ex:
        return False, None, "Not found, error: {}".format(ex)


IS_INSTALLED, VERSION, ERROR = get_version()

if IS_INSTALLED:
    class Z3Proxy(PopenSolverProxy):
        def __init__(self, timeout=None):
            cmd = ['z3', '-smt2', '-in']
            if timeout is not None:
                cmd.append('-t:{}'.format(timeout/1000))  # our timeout is in milliseconds

            p = subprocess.Popen(cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            super(Z3Proxy, self).__init__(p)

    class SolverBackendZ3(SMTLibSolverBackend):
        def solver(self, timeout=None):
            """
            This function should return an instance of whatever object handles
            solving for this backend. For example, in Z3, this would be z3.Solver().
            """
            return Z3Proxy(timeout=timeout)

    from ... import backend_manager as backend_manager
    backend_manager.backends._register_backend(SolverBackendZ3(), 'smtlib_z3', False, False)

else:
    # Z3 is not installed
    log.debug('Z3 not found, corresponding SMTLib backend was disabled! Reason: {}'.format(ERROR))
    pass
