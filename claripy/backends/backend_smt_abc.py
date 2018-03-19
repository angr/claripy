from .backend_smt import BackendSMT
import PythonABCSolver


class BackendSMT_ABC(BackendSMT):
    def __init__(self):
        super(BackendSMT_ABC, self).__init__()
        self.proxy = PythonABCSolver.DriverProxy(0)

    def _satisfiable(self, extra_constraints=(), solver=None, model_callback=None):
        cst_script = self._get_smt_script()
        return self.proxy.isSatisfiable(cst_script)
