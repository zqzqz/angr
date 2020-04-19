import claripy
import cle
from sortedcontainers import SortedDict
from collections import ChainMap
import logging


from ..errors import SimMemoryError, SimSegfaultError, SimMemoryMissingError, SimConcreteMemoryError

from .. import sim_options as options
from .. import global_apis
from .memory_object import SimMemoryObject
from .paged_memory import SimPagedMemory

l = logging.getLogger(name=__name__)

class Segment:
    pass

class SimSegmentedMemory(SimPagedMemory):
    def __init__(self, memory_backer=None, permissions_backer=None, pages=None, initialized=None, name_mapping=None, hash_mapping=None, page_size=None, symbolic_addrs=None, check_permissions=False):
        super(SimSegmentedMemory, self).__init__(memory_backer, permissions_backer, pages, initialized, name_mapping, hash_mapping, page_size, symbolic_addrs, check_permissions)

        self._memory_backer = { } if memory_backer is None else memory_backer
        self._permissions_backer = permissions_backer # saved for copying
        self._check_perms = check_permissions

        self._assoc_pointsto_sets = None

        # For points_to analyse, see analyses/points_to.py
        self._points_to = global_apis.POINTS_TO_ANALYSE
        l.debug(self._points_to)

    def compute_memory_segments(self, args):
        pass

    def get_memory_segment(self, args):
        return Segment()

    def handle_alloc(self, args):
        pass

    # Override other APIs here!
    # def __getstate___(self):
    #     return {
    #         'state1': 'self.state1'
    #     }
    #
    # def __setstate__(self, state):
    #     pass
    #
    # def branch(self):
    #     # more to do and copy but this is a start
    #     m = SimSegmentedMemory(
    #         memory_backer=self._memory_backer,
    #         permissions_backer=self._permissions_backer,
    #         check_permissions=self._check_perms
    #     )
    #     return m
    #
    # def __getitem___(self, addr):
    #     pass
    #
    # def __setitem__(self, addr, v):
    #     pass
    #
    # def load_objects(selfself, addr, num_bytes, ret_on_segv=False):
    #     pass
    #
    # def store_memory_object(self, mo, overwrite=True):
    #     pass
    #
    # def keys(self):
    #     sofar = set()
    #     sofar.update(self._memory_backer.keys())
    #
    #     #they traverse self._pages here
    #
    #     return sofar
