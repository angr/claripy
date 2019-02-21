import subprocess
import logging

import re
from . import SMTLibSolverBackend, PopenSolverProxy
from ...errors import MissingSolverError

log = logging.getLogger(__name__)

def get_version():
    try:
        version_string = subprocess.check_output(['z3', '-version']).decode('utf-8')
        version_match = re.match('Z3 version (.*)\n', version_string)

        if not version_match:
            return False, None, "Found malformed version string: {}".format(version_string)

        return True, version_match.group(1), None

    except subprocess.CalledProcessError as ex:
        return False, None, "Not found, error: {}".format(ex)
    except OSError as ex:
        return False, None, "Not found, error: {}".format(ex)


IS_INSTALLED, VERSION, ERROR = get_version()

class Z3StrProxy(PopenSolverProxy):
    def __init__(self, timeout=None):
        self.timeout = timeout
        self.installed = False
        p = None
        super(Z3StrProxy, self).__init__(p)

    def create_process(self):
        if not IS_INSTALLED:
            raise MissingSolverError('Z3str not found! Please install Z3str before using this backend')
        cmd = ['z3', '-smt2', 'smt.string_solver=z3str3', '-in']
        if self.timeout is not None:
            cmd.append('-t:{}'.format(self.timeout//1000))  # our timeout is in milliseconds

        p = subprocess.Popen(cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        self.installed = False
        return p

class SolverBackendZ3Str(SMTLibSolverBackend):
    def solver(self, timeout=None):
        """
        This function should return an instance of whatever object handles
        solving for this backend. For example, in Z3, this would be z3.Solver().
        """
        return Z3StrProxy(timeout=timeout)

from ... import backend_manager as backend_manager
backend_manager.backends._register_backend(SolverBackendZ3Str(), 'smtlib_z3str', False, False)
