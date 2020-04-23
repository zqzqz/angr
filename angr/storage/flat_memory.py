import claripy
import cle
from sortedcontainers import SortedDict
from collections import ChainMap
import logging
import claripy
import z3

l = logging.getLogger(name=__name__)

from ..errors import SimMemoryError, SimSegfaultError, SimMemoryMissingError, SimConcreteMemoryError

from .. import sim_options as options
from .. import global_apis
from .memory_object import SimMemoryObject
from .paged_memory import SimPagedMemory

l = logging.getLogger(name=__name__)

class SimFlatMemory(SimPagedMemory):
    def __init__(self, memory_backer=None, permissions_backer=None, pages=None, initialized=None, name_mapping=None, hash_mapping=None, page_size=None, symbolic_addrs=None, check_permissions=False):
        super(SimFlatMemory, self).__init__(memory_backer, permissions_backer, pages, initialized, name_mapping, hash_mapping, page_size, symbolic_addrs, check_permissions)
        I = z3.IntSort()
        self.sim_mem_array = z3.Array('sim_mem_array', I, I)
        self.mem_array = []

    # Override other APIs here!

    def store_memory_object(self, mo, overwrite=True):
        super(SimFlatMemory, self).store_memory_object(mo, overwrite)
        index = len(self.mem_array)
        self.mem_array.append(mo)
        self.sim_mem_array = z3.Store(self.sim_mem_array, mo.base, index)
        # for i in range(mo.length):
        #     left = mo.size() - i * mo._byte_width - 1
        #     right = left - mo._byte_width + 1
        #     b = mo.object[left:right]
        #     index = len(self.mem_array)
        #     self.mem_array.append(b)
        #     z3.Store(self.sim_mem_array, mo.base + i, index)

    def load_objects(self, addr, num_bytes, ret_on_segv=False):
        index = z3.simplify(z3.Select(self.sim_mem_array, addr))
        if isinstance(index, z3.z3.IntNumRef):
            l.warn("falt memory load")
            results = []
            for i in range(len(self.mem_array)):
                s = z3.Solver()
                s.add(index == i)
                if s.check() == z3.sat:
                    results.append((addr, self.mem_array[i]))
            return results
        else:
            return super(SimFlatMemory, self).load_objects(addr, num_bytes, ret_on_segv)


