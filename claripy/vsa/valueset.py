import functools
import itertools
import numbers

from ..backend_object import BackendObject
from ..annotation import Annotation

def normalize_types_two_args(f):
    @functools.wraps(f)
    def normalizer(self, region, o):
        """
        Convert any object to an object that we can process.
        """
        if isinstance(o, Base):
            raise ClaripyValueError("BoolResult can't handle AST objects directly")

        if not isinstance(o, StridedInterval):
            raise ClaripyVSAOperationError('Unsupported operand type %s' % type(o))

        return f(self, region, o)

    return normalizer

def normalize_types_one_arg(f):
    @functools.wraps(f)
    def normalizer(self, o):
        """
        Convert any object to an object that we can process.
        """
        if isinstance(o, Base):
            raise ClaripyValueError("BoolResult can't handle AST objects directly")

        return f(self, o)

    return normalizer

vs_id_ctr = itertools.count()


class RegionAnnotation(Annotation):
    """
    Use RegionAnnotation to annotate ASTs. Normally, an AST annotated by RegionAnnotations is treated as a ValueSet.

    Note that Annotation objects are immutable. Do not change properties of an Annotation object without creating a new
    one.
    """

    def __init__(self, region_id, region_base_addr, offset):
        self.region_id = region_id
        self.region_base_addr = region_base_addr
        self.offset = offset

        # Do necessary conversion here
        if isinstance(self.region_base_addr, Base):
            self.region_base_addr = self.region_base_addr._model_vsa
        if isinstance(self.offset, Base):
            self.offset = self.offset._model_vsa

    @property
    def eliminatable(self):
        """
        A Region annotation is not eliminatable in simplifications.

        :return: False
        :rtype: bool
        """

        return False

    @property
    def relocatable(self):
        """
        A Region annotation is not relocatable in simplifications.

        :return: False
        :rtype: bool
        """

        return False

    #
    # Public methods
    #

    def relocate(self, src, dst):
        """
        Override Annotation.relocate().

        :param src: The old AST
        :param dst: The new AST, as the result of a simplification
        :return: The new annotation that should be applied on the new AST
        """

        raise ClaripyVSAError('RegionAnnotation is not relocatable')

    #
    # Overriding base methods
    #

    def __hash__(self):
        return hash((self.region_id, self.region_base_addr, hash(self.offset)))

    def __repr__(self):
        return "<RegionAnnotation %s:%#08x>" % (self.region_id, self.offset)

class ValueSet(BackendObject):
    """
    ValueSet is a mapping between memory regions and corresponding offsets.
    """

    def __init__(self, name=None, region=None, region_base_addr=None, bits=None, val=None):
        """
        Constructor.

        :param str name: Name of this ValueSet object. Only for debugging purposes.
        :param str region: Region ID.
        :param int region_base_addr: Base address of the region.
        :param int bits: Size of the ValueSet.
        :param val: an initial offset
        """

        self._name = 'VS_%d' % next(vs_id_ctr) if name is None else name
        if bits is None:
            raise ClaripyVSAError('bits must be specified when creating a ValueSet.')

        self._bits = bits

        self._si = StridedInterval.empty(bits)
        self._regions = {}
        self._region_base_addrs = {}

        self._reversed = False

        # Shortcuts for initialization
        # May not be useful though...
        if region is not None and region_base_addr is not None and val is not None:
            if isinstance(region_base_addr, numbers.Number):
                # Convert it to a StridedInterval
                region_base_addr = StridedInterval(bits=self._bits, stride=1,
                                                   lower_bound=region_base_addr,
                                                   upper_bound=region_base_addr)

            if isinstance(val, numbers.Number):
                val = StridedInterval(bits=bits, stride=0, lower_bound=val, upper_bound=val)

            if isinstance(val, StridedInterval):
                self._set_si(region, region_base_addr, val)
            else:
                raise ClaripyVSAError("Unsupported type '%s' for argument 'val'" % type(val))

        else:
            if region is not None or val is not None:
                raise ClaripyVSAError("You must specify 'region' and 'val' at the same time.")

    #
    # Properties
    #

    @property
    def name(self):
        return self._name

    @property
    def bits(self):
        return self._bits

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
    def cardinality(self):
        card = 0
        for region in self._regions:
            card += self._regions[region].cardinality

        return card

    @property
    def is_empty(self):
        return len(self._regions) == 0

    @property
    def valueset(self):
        return self

    #
    # Private methods
    #

    def _set_si(self, region, region_base_addr, si):
        if isinstance(si, numbers.Number):
            si = StridedInterval(bits=self.bits, stride=0, lower_bound=si, upper_bound=si)

        if isinstance(region_base_addr, numbers.Number):
            region_base_addr = StridedInterval(bits=self.bits, stride=0, lower_bound=region_base_addr,
                                               upper_bound=region_base_addr
                                               )

        if not isinstance(si, StridedInterval):
            raise ClaripyVSAOperationError('Unsupported type %s for si' % type(si))

        self._regions[region] = si
        self._region_base_addrs[region] = region_base_addr
        self._si = self._si.union(region_base_addr + si)

    def _merge_si(self, region, region_base_addr, si):

        if isinstance(region_base_addr, numbers.Number):
            region_base_addr = StridedInterval(bits=self.bits, stride=0, lower_bound=region_base_addr,
                                               upper_bound=region_base_addr
                                               )

        if region not in self._regions:
            self._set_si(region, region_base_addr, si)
        else:
            self._regions[region] = self._regions[region].union(si)
            self._region_base_addrs[region] = self._region_base_addrs[region].union(region_base_addr)
            self._si = self._si.union(region_base_addr + si)

    #
    # Public methods
    #

    @staticmethod
    def empty(bits):
        return ValueSet(bits=bits)

    def items(self):
        return self._regions.items()

    def size(self):
        return len(self)

    def copy(self):
        """
        Make a copy of self and return.

        :return: A new ValueSet object.
        :rtype: ValueSet
        """

        vs = ValueSet(bits=self.bits)
        vs._regions = self._regions.copy()
        vs._region_base_addrs = self._region_base_addrs.copy()
        vs._reversed = self._reversed
        vs._si = self._si.copy()

        return vs

    def get_si(self, region):
        if region in self._regions:
            return self._regions[region]
        # TODO: Should we return a None, or an empty SI instead?
        return None

    def stridedinterval(self):
        return self._si

    def apply_annotation(self, annotation):
        """
        Apply a new annotation onto self, and return a new ValueSet object.

        :param RegionAnnotation annotation: The annotation to apply.
        :return: A new ValueSet object
        :rtype: ValueSet
        """

        vs = self.copy()
        vs._merge_si(annotation.region_id, annotation.region_base_addr, annotation.offset)
        return vs

    def __repr__(self):
        s = ""
        for region, si in self._regions.items():
            s = "%s: %s" % (region, si)
        return "(" + s + ")"

    def __len__(self):
        return self._bits

    def __hash__(self):
        return hash(tuple((r, hash(self._regions[r])) for r in self._regions))

    #
    # Arithmetic operations
    #

    @normalize_types_one_arg
    def __add__(self, other):
        """
        Binary operation: addition

        Note that even if "other" is a ValueSet object. we still treat it as a StridedInterval. Adding two ValueSets
        together does not make sense (which is essentially adding two pointers together).

        :param StridedInterval other: The other operand.
        :return: A new ValueSet object
        :rtype: ValueSet
        """

        new_vs = ValueSet(bits=self.bits)

        # Call __add__ on self._si
        new_vs._si = self._si.__add__(other)

        for region in self._regions:
            new_vs._regions[region] = self._regions[region] + other

        return new_vs

    @normalize_types_one_arg
    def __radd__(self, other):
        return self.__add__(other)

    @normalize_types_one_arg
    def __sub__(self, other):
        """
        Binary operation: subtraction

        :param other: The other operand
        :return: A StridedInterval or a ValueSet.
        """

        deltas = [ ]

        # TODO: Handle more cases

        if isinstance(other, ValueSet):
            # A subtraction between two ValueSets produces a StridedInterval

            if self.regions.keys() == other.regions.keys():
                for region in self._regions:
                    deltas.append(self._regions[region] - other._regions[region])

            else:
                # TODO: raise the proper exception here
                raise NotImplementedError()

            delta = StridedInterval.empty(self.bits)
            for d in deltas:
                delta = delta.union(d)

            return delta

        else:
            # A subtraction between a ValueSet and a StridedInterval produces another ValueSet

            new_vs = self.copy()

            # Call __sub__ on the base class
            new_vs._si = self._si.__sub__(other)

            for region, si in new_vs._regions.items():
                new_vs._regions[region] = si - other

            return new_vs

    @normalize_types_one_arg
    def __mod__(self, other):
        """
        Binary operation: modulo

        :param other: The other operand
        :return: A StridedInterval or a ValueSet.
        """
        if isinstance(other, ValueSet):
            # TODO: Handle more cases
            raise NotImplementedError()

        else:
            new_vs = self.copy()

            # Call __mode__ on the base class
            new_vs._si = self._si.__mod__(other)

            for region, si in new_vs._regions.items():
                new_vs._regions[region] = si % other

            return new_vs

    @normalize_types_one_arg
    def __and__(self, other):
        """
        Binary operation: and

        Note that even if `other` is a ValueSet object, it will be treated as a StridedInterval as well. Doing & between
        two pointers that are not the same do not make sense.

        :param other: The other operand
        :return: A ValueSet as the result
        :rtype: ValueSet
        """

        if type(other) is ValueSet:
            # The only case where calling & between two points makes sense
            if self.identical(other):
                return self.copy()

        if BoolResult.is_true(other == 0):
            # Corner case: a & 0 = 0
            return StridedInterval(bits=self.bits, stride=0, lower_bound=0, upper_bound=0)

        if BoolResult.is_true(other < 0x100):
            # Special case - sometimes (addr & mask) is used for testing whether the address is aligned or not
            # We return a StridedInterval instead
            ret = None

            for region, si in self._regions.items():
                r = si.__and__(other)
                ret = r if ret is None else ret.union(r)

            return ret

        else:
            # We should return a ValueSet here

            new_vs = self.copy()

            for region, si in self._regions.items():
                r = si.__and__(other)

                new_vs._regions[region] = r

            return new_vs

    def __eq__(self, other):
        """
        Binary operation: ==

        :param other: The other operand
        :return: True/False/Maybe
        """

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
        """
        Binary operation: ==

        :param other: The other operand
        :return: True/False/Maybe
        """

        return ~ (self == other)

    #
    # Backend operations
    #

    def eval(self, n, signed=False):

        if signed:
            # How are you going to deal with a negative pointer?
            raise ClaripyVSAOperationError('`signed` cannot be True when calling ValueSet.eval().')

        results = []

        for _, si in self._regions.items():
            if len(results) < n:
                results.extend(si.eval(n))

        return results

    @property
    def min(self):
        """
        The minimum integer value of a value-set. It is only defined when there is exactly one region.

        :return: A integer that represents the minimum integer value of this value-set.
        :rtype:  int
        """

        if len(self.regions) != 1:
            raise ClaripyVSAOperationError("'min()' onlly works on single-region value-sets.")

        return self.get_si(next(iter(self.regions))).min

    @property
    def max(self):
        """
        The maximum integer value of a value-set. It is only defined when there is exactly one region.

        :return: A integer that represents the maximum integer value of this value-set.
        :rtype:  int
        """

        if len(self.regions) != 1:
            raise ClaripyVSAOperationError("'max()' onlly works on single-region value-sets.")

        return self.get_si(next(iter(self.regions))).max

    def reverse(self):
        # TODO: obviously valueset.reverse is not properly implemented. I'm disabling the old annoying output line for
        # TODO: now. I will implement the proper reversing support soon.
        vs = self.copy()
        vs._reversed = not vs._reversed

        return vs

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
                new_vs._set_si(region, self._region_base_addrs[region], si.concat(b))

        elif isinstance(b, ValueSet):
            for region, si in self._regions.items():
                new_vs._set_si(region, self._region_base_addrs[region], si.concat(b.get_si(region)))

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

                merged_vs._si = merged_vs._si.union(b._si)

        else:
            for region, si in merged_vs._regions.items():
                merged_vs._regions[region] = merged_vs._regions[region].union(b)

            merged_vs._si = merged_vs._si.union(b)

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

            merged_vs._si = merged_vs._si.widen(b._si)

        else:
            for region in merged_vs._regions:
                merged_vs._regions[region] = merged_vs._regions[region].widen(b)

            merged_vs._si = merged_vs._si.widen(b)

        return merged_vs

    @normalize_types_one_arg
    def intersection(self, b):
        vs = self.copy()

        if isinstance(b, ValueSet):
            for region, si in b.regions.items():
                if region not in vs.regions:
                    pass
                else:
                    vs.regions[region] = vs.regions[region].intersection(si)

                    if vs.regions[region].is_empty:
                        del vs.regions[region]

            vs._si = vs._si.intersection(b._si)

        else:
            for region in self._regions:
                vs.regions[region] = vs.regions[region].intersection(b)

                if vs.regions[region].is_empty:
                    del vs.regions[region]

            vs._si = vs._si.intersection(b)

        return vs

    def identical(self, o):
        """
        Used to make exact comparisons between two ValueSets.

        :param o:   The other ValueSet to compare with.
        :return:    True if they are exactly same, False otherwise.
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


from ..ast.base import Base
from .strided_interval import StridedInterval
from .bool_result import BoolResult, TrueResult, FalseResult, MaybeResult
from .errors import ClaripyVSAOperationError, ClaripyVSAError
from ..errors import ClaripyValueError
