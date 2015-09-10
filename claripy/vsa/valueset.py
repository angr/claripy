import functools
import itertools
from ..backend_object import BackendObject

def normalize_types(f):
    @functools.wraps(f)
    def normalizer(self, region, o):
        '''
        Convert any object to an object that we can process.
        '''
        if isinstance(o, IfProxy):
            return NotImplemented

        if isinstance(o, Base):
            o = o.model

        if not isinstance(o, StridedInterval):
            raise ClaripyVSAOperationError('Unsupported operand type %s' % type(o))

        return f(self, region, o)

    return normalizer

def normalize_types_one_arg(f):
    @functools.wraps(f)
    def normalizer(self, o):
        '''
        Convert any object to an object that we can process.
        '''
        if isinstance(o, IfProxy):
            return NotImplemented

        if isinstance(o, Base):
            o = o.model

        return f(self, o)

    return normalizer

vs_id_ctr = itertools.count()

class ValueSet(BackendObject):
    def __init__(self, name=None, region=None, bits=None, val=None):
        self._name = name
        if self._name is None:
            self._name = 'VS_%d' % vs_id_ctr.next()

        self._regions = {}

        self._reversed = False
        if bits is None:
            if val is None:
                raise ClaripyVSAError("Either 'size' or 'val' must be specified.")
            else:
                self._bits = val.bits()

        else:
            self._bits = bits

        if region is not None and val is not None:
            if isinstance(val, (StridedInterval, IfProxy)):
                self.set_si(region, val)

            elif type(val) in (int, long):
                self.set_si(region, StridedInterval(bits=bits, stride=0, lower_bound=val, upper_bound=val))

            else:
                raise ClaripyVSAError("Unsuported type '%s' for argument 'val'" % type(val))

        else:
            if region is not None or val is not None:
                raise ClaripyVSAError("You must specify 'region' and 'val' at the same time.")

    @property
    def name(self):
        return self._name

    @property
    def regions(self):
        return self._regions

    @property
    def reversed(self):
        return self._reversed

    @property
    def unique(self):
        return len(self.regions) == 1 and self.regions.values()[0].unique

    @property
    def bits(self):
        return self.size()

    @normalize_types
    def set_si(self, region, si):
        if not isinstance(si, StridedInterval):
            raise ClaripyVSAOperationError('Unsupported type %s for si' % type(si))

        self._regions[region] = si

    def get_si(self, region):
        if region in self._regions:
            return self._regions[region]
        # TODO: Should we return a None, or an empty SI instead?
        return None

    def items(self):
        return self._regions.items()

    def size(self):
        return len(self)

    @normalize_types
    def merge_si(self, region, si):
        if region not in self._regions:
            self.set_si(region, si)
        else:
            self._regions[region] = self._regions[region].union(si)

    @normalize_types
    def remove_si(self, region, si):
        raise NotImplementedError()

    def __repr__(self):
        s = ""
        for region, si in self._regions.items():
            s = "%s: %s" % (region, si)
        return "(" + s + ")"

    def __len__(self):
        return self._bits

    @normalize_types_one_arg
    def __add__(self, other):
        if type(other) is ValueSet:
            # Normally, addition between two addresses doesn't make any sense.
            # So we only handle those corner cases

            raise NotImplementedError()
        else:
            new_vs = ValueSet(bits=self.bits)
            for region, si in self._regions.items():
                new_vs._regions[region] = si + other

            return new_vs

    @normalize_types_one_arg
    def __radd__(self, other):
        return self.__add__(other)

    @normalize_types_one_arg
    def __sub__(self, other):
        """
        Binary operation: subtraction

        :param other: The other operand
        :return: A StridedInterval.
        """

        deltas = [ ]

        # TODO: Handle more cases

        if type(other) is ValueSet:
            # A subtraction between two ValueSets produces a StridedInterval

            if self.regions.keys() == other.regions.keys():
                for region, si in self._regions.iteritems():
                    deltas.append(si - other._regions[region])

            else:
                __import__('ipdb').set_trace()
                raise NotImplementedError()

            delta = StridedInterval.empty(self.bits)
            for d in deltas:
                delta = delta.union(d)

            return delta

        else:
            # A subtraction between a ValueSet and an StridedInterval produces another ValueSet

            new_vs = self.copy()
            for region, si in new_vs._regions.items():
                new_vs._regions[region] = si - other

            return new_vs

    @normalize_types_one_arg
    def __and__(self, other):
        if type(other) is ValueSet:
            if self.identical(other):
                return self.copy()
            raise NotImplementedError("__and__(vs1, vs2)?")

        if BoolResult.is_true(other == 0):
            # Corner case: a & 0 = 0
            return StridedInterval(bits=self.bits, stride=0, lower_bound=0, upper_bound=0)

        new_vs = ValueSet(bits=self.bits)
        if BoolResult.is_true(other < 0x100):
            # Special case - sometimes (addr & mask) is used for testing whether the address is aligned or not
            # We return an SI instead
            ret = None

            for region, si in self._regions.items():
                r = si.__and__(other)

                ret = r if ret is None else ret.union(r)

            return ret

        else:
            for region, si in self._regions.items():
                r = si.__and__(other)

                new_vs._regions[region] = r

            return new_vs

    def __eq__(self, other):
        if isinstance(other, ValueSet):
            same = False
            different = False
            for region, si in other.regions.items():
                if region in self.regions:
                    comp_ret = self.regions[region] == si
                    if BoolResult.has_true(comp_ret):
                        same = True
                    if BoolResult.has_false(comp_ret):
                        different = True
                else:
                    different = True

            if same and not different:
                return TrueResult()
            if same and different:
                return MaybeResult()
            return FalseResult()
        elif isinstance(other, StridedInterval):
            if 'global' in self.regions:
                return self.regions['global'] == other
            else:
                return FalseResult()
        else:
            return FalseResult()

    def __ne__(self, other):
        return ~ (self == other)

    def eval(self, n):
        results = []

        for _, si in self._regions.items():
            if len(results) < n:
                results.extend(si.eval(n))

        return results

    def copy(self):
        vs = ValueSet(bits=self.bits)
        vs._regions = self._regions.copy()
        vs._reversed = self._reversed

        return vs

    def reverse(self):
        # TODO: obviously valueset.reverse is not properly implemented. I'm disabling the old annoying output line for
        # TODO: now. I will implement the proper reversing support soon.
        vs = self.copy()
        vs._reversed = not vs._reversed

        return vs

    @property
    def is_empty(self):
        return len(self._regions) == 0

    def extract(self, high_bit, low_bit):
        """
        Operation extract

        - A cheap hack is implemented: a copy of self is returned if (high_bit - low_bit + 1 == self.bits), which is a
            ValueSet instance. Otherwise a StridedInterval is returned.

        :param high_bit:
        :param low_bit:
        :return: A ValueSet or a StridedInterval
        """

        if high_bit - low_bit + 1 == self.bits:
            return self.copy()

        if ('global' in self._regions and len(self._regions.keys()) > 1) or \
            len(self._regions.keys()) > 0:
            si_ret = StridedInterval.top(high_bit - low_bit + 1)

        else:
            if 'global' in self._regions:
                si = self._regions['global']
                si_ret = si.extract(high_bit, low_bit)

            else:
                si_ret = StridedInterval.empty(high_bit - low_bit + 1)

        return si_ret

    def concat(self, b):
        new_vs = ValueSet(bits=self.bits + b.bits)
        # TODO: This logic is obviously flawed. Correct it later :-(
        if isinstance(b, StridedInterval):
            for region, si in self._regions.items():
                new_vs.set_si(region, si.concat(b))

        elif isinstance(b, ValueSet):
            for region, si in self._regions.items():
                new_vs.set_si(region, si.concat(b.get_si(region)))

        else:
            raise ClaripyVSAOperationError('ValueSet.concat() got an unsupported operand %s (type %s)' % (b, type(b)))

        return new_vs

    @normalize_types_one_arg
    def union(self, b):
        merged_vs = self.copy()
        if type(b) is ValueSet:
            for region, si in b.regions.items():
                if region not in merged_vs._regions:
                    merged_vs._regions[region] = si
                else:
                    merged_vs._regions[region] = merged_vs._regions[region].union(si)
        else:
            for region, si in self._regions.items():
                merged_vs._regions[region] = merged_vs._regions[region].union(b)

        return merged_vs

    @normalize_types_one_arg
    def widen(self, b):
        merged_vs = self.copy()
        if isinstance(b, ValueSet):
            for region, si in b.regions.items():
                if region not in merged_vs.regions:
                    merged_vs.regions[region] = si
                else:
                    merged_vs.regions[region] = merged_vs.regions[region].widen(si)

        else:
            for region, si in self._regions.iteritems():
                merged_vs._regions[region] = merged_vs._regions[region].widen(b)

        return merged_vs

    def identical(self, o):
        """
        Used to make exact comparisons between two ValueSets.

        :param o: The other ValueSet to compare with
        :return: True if they are exactly same, False otherwise
        """
        if self._reversed != o._reversed:
            return False

        for region, si in self.regions.items():
            if region in o.regions:
                o_si = o.regions[region]
                if not si.identical(o_si):
                    return False
            else:
                return False

        return True

    def __hash__(self):
        return hash(tuple([ (r, hash(si)) for r, si in self._regions.iteritems() ]))

from ..ast.base import Base
from .strided_interval import StridedInterval
from .ifproxy import IfProxy
from .bool_result import BoolResult, TrueResult, FalseResult, MaybeResult
from .errors import ClaripyVSAOperationError, ClaripyVSAError
