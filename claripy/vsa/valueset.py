import functools

def normalize_types(f):
    @functools.wraps(f)
    def normalizer(self, region, o):
        '''
        Convert any object to an object that we can process.
        '''
        if type(o) is E:
            o = o._model

        assert type(o) is StridedInterval

        return f(self, region, o)

    return normalizer

class ValueSet(object):
    def __init__(self):
        self._si_dict = {}

    @normalize_types
    def set_si(self, region, si):
        self._si_dict[region] = si

    def get_si(self, region):
        if region in self._si_dict:
            return self._si_dict[region]
        # TODO: Should we return a None, or an empty SI instead?
        return None

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
        for region, si in self._si_dict.items():
            s = "%s: %s" % (region, si)
        return "(" + s + ")"

    def __len__(self):
        if self.is_empty():
            return 0
        return len(self._si_dict.items()[0][1])

    def is_empty(self):
        return (len(self._si_dict) == 0)

from .strided_interval import StridedInterval
from ..expression import E