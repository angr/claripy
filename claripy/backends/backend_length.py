from . import Backend
class BackendLength(Backend):
    def __init__(self):
        Backend.__init__(self)
        self._op_expr['BVS'] = self.length_bv
        self._op_expr['BVV'] = self.length_bv
        self._op_expr['BoolV'] = self.length_none
        self._op_expr['BoolS'] = self.length_none
        self._op_expr['FPV'] = self.length_fp
        self._op_expr['FPS'] = self.length_fp

        self._op_expr['fpToFP'] = self.length_fp_conversion
        self._op_expr['fpToFPUnsigned'] = self.length_fp_conversion
        self._op_raw['fpToIEEEBV'] = self.length_same
        self._op_expr['fpToSBV'] = self.length_fpToBV
        self._op_expr['fpToUBV'] = self.length_fpToBV

        for o in operations.length_same_operations:
            self._op_raw[o] = self.length_same
        for o in operations.length_none_operations:
            self._op_raw[o] = self.length_none

        self._op_raw['fpFP'] = self.length_fp_fp
        self._op_raw['Concat'] = self.length_concat
        self._op_raw['Extract'] = self.length_extract
        self._op_expr['SignExt'] = self.length_extend
        self._op_expr['ZeroExt'] = self.length_extend

    def _convert(self, a): #pylint:disable=unused-argument
        return None

    @staticmethod
    def length_bv(s):
        return s.args[1]
    @staticmethod
    def length_fp(s):
        return s.args[1].length

    @staticmethod
    def length_fp_conversion(*args):
        return args[-1].length

    @staticmethod
    def length_fp_fp(*args):
        return sum(args)

    @staticmethod
    def length_fpToBV(_rm, _fp, length):
        return length

    @staticmethod
    def length_none(*args): #pylint:disable=unused-argument
        return None

    @staticmethod
    def length_same(*args):
        """
        Verify and return the length of length-preserving operations.
        """
        lengthed = [ a for a in args if a is not None ]
        if len(set(lengthed)) != 1:
            raise ClaripyOperationError("Encountered an invalid length combination when processing an expression.")
        return lengthed[0]

    @staticmethod
    def length_extract(high, low, original):
        if high < 0 or low < 0:
            raise ClaripyOperationError("Extract high and low bit indices must be nonnegative")
        elif low > high:
            raise ClaripyOperationError("Extract low bit index must be <= high bit index")
        elif high >= original:
            return ClaripyOperationError("Extract bound must be less than BV size")

        return high - low + 1

    def length_extend(self, s):
        return s.args[0] + self.convert(s.args[1])

    @staticmethod
    def length_concat(*args):
        return sum(args)

from ..errors import ClaripyOperationError
from .. import operations
