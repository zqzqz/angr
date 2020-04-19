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
        super().__init__(memory_backer, permissions_backer, pages, initialized, name_mapping, hash_mapping, page_size, symbolic_addrs, check_permissions)

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

