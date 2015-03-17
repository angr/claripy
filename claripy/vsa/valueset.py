import functools
import itertools
from ..backend import BackendObject

def normalize_types(f):
    @functools.wraps(f)
    def normalizer(self, region, o):
        '''
        Convert any object to an object that we can process.
        '''
        if isinstance(o, IfProxy):
            return NotImplemented

        if isinstance(o, A):
            o = o.model

        assert type(o) is StridedInterval

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

        if isinstance(o, A):
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

        if region is not None and bits is not None and val is not None:
            self.set_si(region, StridedInterval(bits=bits, stride=0, lower_bound=val, upper_bound=val))

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
        if self.is_empty():
            return 0
        return len(self._regions.items()[0][1])

    @normalize_types_one_arg
    def __add__(self, other):
        if type(other) is ValueSet:
            raise NotImplementedError()
        else:
            new_vs = ValueSet()
            for region, si in self._regions.items():
                new_vs._regions[region] = si + other

            return new_vs

    @normalize_types_one_arg
    def __radd__(self, other):
        return self.__add__(other)

    @normalize_types_one_arg
    def __sub__(self, other):
        if type(other) is ValueSet:
            raise NotImplementedError()
        else:
            new_vs = ValueSet()
            for region, si in self._regions.items():
                new_vs._regions[region] = si - other

            return new_vs

    @normalize_types_one_arg
    def __and__(self, other):
        if type(other) is ValueSet:
            # An address bitwise-and another address? WTF?
            assert False

        new_vs = ValueSet()
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
        vs = ValueSet()
        vs._regions = self._regions.copy()
        vs._reversed = self._reversed

        return vs

    def reverse(self):
        print "valueset.reverse is not properly implemented"
        vs = self.copy()
        vs._reversed = not vs._reversed

        return vs

    def is_empty(self):
        return len(self._regions) == 0

    def extract(self, high_bit, low_bit):
        new_vs = ValueSet()
        for region, si in self._regions.items():
            new_vs.set_si(region, si.extract(high_bit, low_bit))

        return new_vs

    def concat(self, b):
        new_vs = ValueSet()
        # TODO: This logic is obviously flawed. Correct it later :-(
        for region, si in self._regions.items():
            new_vs.set_si(region, si.concat(b.get_si(region)))

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
        for region, si in b.regions.items():
            if region not in merged_vs.regions:
                merged_vs.regions[region] = si
            else:
                merged_vs.regions[region] = merged_vs.regions[region].widen(si)

        return merged_vs

from ..ast import A
from .strided_interval import StridedInterval
from .ifproxy import IfProxy
from .bool_result import BoolResult, TrueResult, FalseResult, MaybeResult
