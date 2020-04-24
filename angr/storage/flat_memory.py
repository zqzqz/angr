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
    def __init__(self, sim_mem_array=None, mem_array=None, memory_backer=None, permissions_backer=None, pages=None, initialized=None, name_mapping=None, hash_mapping=None, page_size=None, symbolic_addrs=None, check_permissions=False):
        super(SimFlatMemory, self).__init__(memory_backer, permissions_backer, pages, initialized, name_mapping, hash_mapping, page_size, symbolic_addrs, check_permissions)
        self._sim_mem_array = z3.Array('sim_mem_array', z3.IntSort(), z3.IntSort()) if sim_mem_array is None else sim_mem_array
        self._mem_array = [] if mem_array is None else mem_array

    # Override other APIs here!
    def __getstate__(self):
        return {
            '_memory_backer': self._memory_backer,
            '_permissions_backer': self._permissions_backer,
            '_executable_pages': self._executable_pages,
            '_permission_map': self._permission_map,
            '_pages': self._pages,
            '_initialized': self._initialized,
            '_page_size': self._page_size,
            'state': None,
            '_name_mapping': self._name_mapping,
            '_hash_mapping': self._hash_mapping,
            '_symbolic_addrs': self._symbolic_addrs,
            '_preapproved_stack': self._preapproved_stack,
            '_check_perms': self._check_perms,
            '_sim_mem_array': self._sim_mem_array,
            '_mem_array': self._mem_array
        }

    def branch(self):
        new_name_mapping = self._name_mapping.new_child() if options.REVERSE_MEMORY_NAME_MAP in self.state.options else self._name_mapping
        new_hash_mapping = self._hash_mapping.new_child() if options.REVERSE_MEMORY_HASH_MAP in self.state.options else self._hash_mapping

        new_pages = dict(self._pages)
        self._cowed = set()
        m = SimFlatMemory(memory_backer=self._memory_backer,
                           permissions_backer=self._permissions_backer,
                           pages=new_pages,
                           initialized=set(self._initialized),
                           page_size=self._page_size,
                           name_mapping=new_name_mapping,
                           hash_mapping=new_hash_mapping,
                           symbolic_addrs=dict(self._symbolic_addrs),
                           check_permissions=self._check_perms,
                           sim_mem_array=self._sim_mem_array,
                           mem_array=self._mem_array)
        m._preapproved_stack = self._preapproved_stack
        return m


    def store_memory_object(self, mo, overwrite=True):
        super(SimFlatMemory, self).store_memory_object(mo, overwrite)
        for i in range(mo.length):
            b = mo.bytes_at(mo.base+i,1)
            index = len(self._mem_array)
            self._mem_array.append(b)
            self._sim_mem_array = z3.Store(self._sim_mem_array, mo.base + i, index)

    def load_memory_object(self, addr, num_bytes):
        if isinstance(addr, claripy.ast.bv.BV):
            addr = self.state.solver.eval(addr)
        if isinstance(addr, claripy.ast.bv.BV):
            # no such interface
            return None, []
        error = False
        result = claripy.BVV(0x00, 0)
        for i in range(num_bytes):
            index = z3.simplify(z3.Select(self._sim_mem_array, addr+i))
            if isinstance(index, z3.z3.IntNumRef):
                result = result.concat(self._mem_array[int(index.as_string())])
            else:
                error = True
                break
        if error:
            return None, None
        else:
            l.warn("falt memory load")
            return result, []


