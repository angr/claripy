import logging
import subprocess

from claripy import backend_manager as backend_manager
from claripy.errors import MissingSolverError

from . import PopenSolverProxy, SMTLibSolverBackend

log = logging.getLogger(__name__)


def get_version():
    try:
        subprocess.check_output(["abc", "--help"]).decode("utf-8")
        # version_string = subprocess.check_output(["abc", "--help"]).decode("utf-8")
        # version_match = re.match('This is CVC4 version (.*)\n', version_string)

        # if not version_match:
        #    return False, None, "Found malformed version string: {}".format(version_string)

        return True, None, None  # True, version_match.group(1), None

    except subprocess.CalledProcessError as ex:
        return False, None, f"Not found, error: {ex}"
    except OSError as ex:
        return False, None, f"Not found, error: {ex}"


IS_INSTALLED, VERSION, ERROR = get_version()


class ABCProxy(PopenSolverProxy):
    def __init__(self):
        self.installed = False
        p = None
        super().__init__(p)

    def create_process(self):
        if not IS_INSTALLED:
            raise MissingSolverError("ABC not found! Please install ABC before using this backend")
        p = subprocess.Popen(["abc"], stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        self.installed = True
        return p


class SolverBackendABC(SMTLibSolverBackend):
    def solver(self, timeout=None, max_memory=None):
        """
        This function should return an instance of whatever object handles
        solving for this backend. For example, in Z3, this would be z3.Solver().
        """
        return ABCProxy()


backend_manager.backends._register_backend(SolverBackendABC(), "smtlib_abc", False, False)
