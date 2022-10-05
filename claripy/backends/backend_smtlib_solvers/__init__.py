import hashlib

import os

from claripy.ast.bv import BV

from .. import BackendError
from ..backend_smtlib import BackendSMTLibBase
from ...smtlib_utils import SMTParser, make_pysmt_const_from_type
from six.moves import cStringIO

from pysmt.smtlib.parser import Tokenizer
from pysmt.shortcuts import NotEquals


class AbstractSMTLibSolverProxy(object):
    def write(self, smt):
        raise NotImplementedError

    def read(self, n):
        raise NotImplementedError

    def setup(self):
        pass

    def reset(self):
        self.write('(reset)\n')

    def readuntil(self, s):
        buf = b''
        s = s.encode()
        while s not in buf:
            buf += self.read(1)
        return buf

    def readline(self):
        return self.readuntil('\n')

    def writeline(self, l):
        return self.write(l + '\n')

    def read_sat(self):
        return self.readline().strip().decode('utf-8')

    def read_model(self):
        read_model = self.readuntil('\n)\n').strip().decode('utf-8')
        return read_model

    def create_process(self):
        raise NotImplementedError

class PopenSolverProxy(AbstractSMTLibSolverProxy):
    def __init__(self, p):
        super(PopenSolverProxy, self).__init__()
        self.p = p
        self.constraints = []

    def read(self, n):
        if self.p is None:
            self.p = self.create_process()
        return self.p.stdout.read(n)

    def write(self, smt):
        if self.p is None:
            self.p = self.create_process()
        self.p.stdin.write(smt.encode())
        self.p.stdin.flush()

    def add_constraints(self, csts, track=False):
        self.constraints.extend(csts)

    def terminate(self):
        self.p.terminate()
        self.p = None


class SMTLibSolverBackend(BackendSMTLibBase):
    def __init__(self, *args, **kwargs):
        kwargs['solver_required'] = True
        self.smt_script_log_dir = kwargs.pop('smt_script_log_dir', None)
        super(SMTLibSolverBackend, self).__init__(*args, **kwargs)

    def solver(self, timeout=None, max_memory=None): #pylint:disable=no-self-use,unused-argument
        """
        This function should return an instance of whatever object handles
        solving for this backend. For example, in Z3, this would be z3.Solver().
        """
        raise NotImplementedError

    def _get_primitive_for_expr(self, model, e):
        substituted = e.substitute(model).simplify()
        if not substituted.is_constant():
            raise BackendError(
                "CVC4 backend currently only supports requests for symbols directly! This is a weird one that doesn't "
                "turn constant after substitution??")

        return substituted.constant_value()

    def _simplify(self, e):
        return e

    def _is_false(self, e, extra_constraints=(), solver=None, model_callback=None):
        if e.is_constant() and e.constant_value() is False:
            return True
        return False

    def _is_true(self, e, extra_constraints=(), solver=None, model_callback=None):
        if e.is_constant() and e.constant_value() is True:
            return True
        return False

    def _batch_eval(self, exprs, n, extra_constraints=(), solver=None, model_callback=None):
        return [self._eval(e, n, extra_constraints=extra_constraints, solver=solver, model_callback=model_callback) for e in exprs]

    def _add(self, s, c, track=False):
        s.add_constraints(c, track=track)

    def _check_satness(self, solver=None, extra_constraints=(), model_callback=None, extra_variables=()):
        vars, csts = self._get_all_vars_and_constraints(solver=solver, e_c=extra_constraints, e_v=extra_variables)
        smt_script = self._get_satisfiability_smt_script(constraints=csts, variables=vars)

        if self.smt_script_log_dir is not None:
            fname = 'check-sat_{}.smt2'.format(hashlib.md5(smt_script.encode()).hexdigest())

            with open(os.path.join(self.smt_script_log_dir, fname), 'wb') as f:
                f.write(smt_script.encode())

        solver.reset()
        solver.write(smt_script)

        sat = solver.read_sat().upper()
        if sat not in {'SAT', 'UNSAT', 'UNKNOWN'}:
            raise ValueError("Solver error, don't understand (check-sat) response: {}".format(repr(sat)))
        return sat.upper()

    def _check_satisfiability(self, extra_constraints=(), solver=None, model_callback=None, extra_variables=()):
        satness = self._check_satness(solver, extra_constraints, model_callback, extra_variables)
        return satness

    def _satisfiable(self, solver=None, extra_constraints=(), model_callback=None, extra_variables=()):
        satness = self._check_satness(solver, extra_constraints, model_callback, extra_variables)
        # solver is done, terminate process
        solver.terminate()

        return satness == 'SAT'

    def _get_model(self, solver=None, extra_constraints=(), extra_variables=()):
        vars, csts = self._get_all_vars_and_constraints(solver=solver, e_c=extra_constraints, e_v=extra_variables)
        smt_script = self._get_full_model_smt_script(constraints=csts, variables=vars)
        if self.smt_script_log_dir is not None:
            fname = 'get-model_{}.smt2'.format(hashlib.md5(smt_script.encode()).hexdigest())
            with open(os.path.join(self.smt_script_log_dir, fname), 'wb') as f:
                f.write(smt_script.encode())

        solver.reset()
        solver.write(smt_script)

        sat = solver.read_sat()
        if sat == 'sat':
            model_string = solver.read_model()
            tokens = Tokenizer(cStringIO(model_string), interactive=True)
            ass_list = SMTParser(tokens).consume_assignment_list()
            return sat, {s: val for s, val in ass_list}, ass_list
        else:
            error = solver.readline()

        return sat, error, None

    def _eval(self, expr, n, extra_constraints=(), solver=None, model_callback=None):
        e_c = list(extra_constraints)

        if expr.is_constant():
            return [expr.constant_value()]

        expr_vars = expr.get_free_variables()

        results = []
        while len(results) < n:
            sat, model, ass_list = self._get_model(solver=solver, extra_constraints=e_c, extra_variables=expr_vars)
            if sat != 'sat':
                break

            val = self._get_primitive_for_expr(model, expr)

            if val in results:
                # import ipdb; ipdb.set_trace()
                raise ValueError("Solver error, solver returned the same value twice incorrectly!")

            results.append(val)
            # e_c.append(And(*[NotEquals(s, val) for s, val in ass_list]))
            e_c.append(NotEquals(make_pysmt_const_from_type(val, expr.get_type()), expr))

        return tuple(results)

    def eval(self, expr, n, extra_constraints=(), solver=None, model_callback=None):
        """
        This function returns up to `n` possible solutions for expression `expr`.

        :param expr: expression (an AST) to evaluate
        :param n: number of results to return
        :param solver: a solver object, native to the backend, to assist in
                       the evaluation (for example, a z3.Solver)
        :param extra_constraints: extra constraints (as ASTs) to add to the solver for this solve
        :param model_callback:      a function that will be executed with recovered models (if any)
        :return:              A sequence of up to n results (backend objects)
        """
        if self._solver_required and solver is None:
            raise BackendError("%s requires a solver for evaluation" % self.__class__.__name__)

        results = self._eval(
            self.convert(expr), n, extra_constraints=self.convert_list(extra_constraints),
            solver=solver, model_callback=model_callback
        )

        results = list(results)
        if type(expr) is not BV:
            return results

        size = expr.length
        for i in range(len(results)):
            results[i] &= (1 << size) - 1 # convert it back to unsigned

        # solver is done, terminate process
        solver.terminate()

        return results

from . import cvc4_popen
from . import z3_popen
from . import abc_popen
from . import z3str_popen
