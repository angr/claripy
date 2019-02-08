import subprocess
import logging

import re
from . import SMTLibSolverBackend, PopenSolverProxy
from ...errors import MissingSolverError

log = logging.getLogger(__name__)

def get_version():
    try:
        version_string = subprocess.check_output(['cvc4', '--version']).decode('utf-8')
        version_match = re.match('This is CVC4 version (.*)\n', version_string)

        if not version_match:
            return False, None, "Found malformed version string: {}".format(version_string)

        return True, version_match.group(1), None

    except subprocess.CalledProcessError as ex:
        return False, None, "Not found, error: {}".format(ex)
    except OSError as ex:
        return False, None, "Not found, error: {}".format(ex)


IS_INSTALLED, VERSION, ERROR = get_version()

class CVC4Proxy(PopenSolverProxy):
    def __init__(self, timeout=None):
        # lazy instantiation: Here we don't spawn the subprocess
        self.timeout = timeout
        self.installed = False
        p = None
        super(CVC4Proxy, self).__init__(p)

    def create_process(self):
        # spawn the subprocess
        if not IS_INSTALLED:
            raise MissingSolverError('CVC4 not found! Please install CVC4 before using this backend')
        cmd = ['cvc4', '--lang=smt', '-q', '--strings-exp']
        if self.timeout is not None:
            cmd += ['--tlimit-per={}'.format(self.timeout)]
        p = subprocess.Popen(cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        self.installed = True
        return p

class SolverBackendCVC4(SMTLibSolverBackend):
    def solver(self, timeout=None):
        """
        This function should return an instance of whatever object handles
        solving for this backend. For example, in Z3, this would be z3.Solver().
        """
        return CVC4Proxy(timeout)

from ... import backend_manager as backend_manager
backend_manager.backends._register_backend(SolverBackendCVC4(), 'smtlib_cvc4', False, False)
