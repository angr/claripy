import functools

def normalize_types(f):
    @functools.wraps(f)
    def normalizer(self, region, o):
        '''
        Convert any object to an object that we can process.
        '''
        if type(o) is E:
            o = o.model

        assert type(o) is StridedInterval

        return f(self, region, o)

    return normalizer

class ValueSet(object):
    def __init__(self, region=None, bits=None, val=None):
        self._si_dict = {}

        self._reversed = False

        if region is not None and bits is not None and val is not None:
            self.set_si(region, StridedInterval(bits=bits, stride=0, lower_bound=val, upper_bound=val))

    @normalize_types
    def set_si(self, region, si):
        self._si_dict[region] = si

    def get_si(self, region):
        if region in self._si_dict:
            return self._si_dict[region]
        # TODO: Should we return a None, or an empty SI instead?
        return None

    def items(self):
        return self._si_dict.items()

    def size(self):
        return len(self)

    @normalize_types
    def merge_si(self, region, si):
        if region not in self._si_dict:
            self.set_si(region, si)
        else:
            self._si_dict[region] = self._si_dict[region].union(si)

    @normalize_types
    def remove_si(self, region, si):
        raise NotImplementedError()

    def __repr__(self):
        s = ""
        for region, si in self._si_dict.items():
            s = "%s: %s" % (region, si)
        return "(" + s + ")"

    def __len__(self):
        if self.is_empty():
            return 0
        return len(self._si_dict.items()[0][1])

    def __add__(self, other):
        if type(other) is ValueSet:
            raise NotImplementedError()
        else:
            new_vs = ValueSet()
            for region, si in self._si_dict.items():
                new_vs._si_dict[region] = si + other

            return new_vs

    def __sub__(self, other):
        if type(other) is ValueSet:
            raise NotImplementedError()
        else:
            new_vs = ValueSet()
            for region, si in self._si_dict.items():
                new_vs._si_dict[region] = si - other

            return new_vs

    def __and__(self, other):
        if type(other) is ValueSet:
            # An address bitwise-and another address? WTF?
            assert False

        new_vs = ValueSet()
        for region, si in self._si_dict.items():
            new_vs._si_dict[region] = si.__and__(other)

        return new_vs

    def copy(self):
        vs = ValueSet()
        vs._si_dict = self._si_dict.copy()
        vs._reversed = self._reversed

        return vs

    def reverse(self):
        vs = self.copy()

        vs._reversed = not vs._reversed

        return vs

    def is_empty(self):
        return (len(self._si_dict) == 0)

    def extract(self, high_bit, low_bit):
        new_vs = ValueSet()
        for region, si in self._si_dict.items():
            new_vs.set_si(region, si.extract(high_bit, low_bit))

        return new_vs

    def concat(self, b):
        new_vs = ValueSet()
        # TODO: This logic is obviously flawed. Correct it later :-(
        for region, si in self._si_dict.items():
            new_vs.set_si(region, si.concat(b.get_si(region)))

        return new_vs

    def reverse(self):
        #import ipdb; ipdb.set_trace()
        print "valueset.reverse is not implemented"
        return self

from .strided_interval import StridedInterval
from ..expression import E
