import claripy
import cle
from sortedcontainers import SortedDict
from collections import ChainMap
import logging
import claripy
import copy


from ..errors import SimMemoryError, SimSegfaultError, SimMemoryMissingError, SimConcreteMemoryError

from .. import sim_options as options
from .. import global_apis
from .memory_object import SimMemoryObject
from .paged_memory import SimPagedMemory

l = logging.getLogger(name=__name__)

class Segment:
    def __init__(self, mem_array=None):
        self._mem_array = {} if mem_array is None else mem_array
        self._addr = 0
        self._length = 0

    def store_memory_object(self, data, addr, size, init=False):
        if not isinstance(size, int):
            return

        if init:
            # assume allocation only has concrete address 
            if not isinstance(addr, int):
                return
            self._addr = addr
            self._length = size

        byte_width = 8
        for i in range(size):
            if isinstance(data, bytes):
                b = data[i*byte_width:(i+1)*byte_width]
            else:
                left = size * byte_width - i * byte_width - 1
                right = left - byte_width + 1
                b = data[left:right]
            a = addr + i
            if isinstance(a, int):
                self._mem_array[a] = b
            else:
                for key in list(self._mem_array.keys()):
                    if not claripy.is_false(a == key):
                        self._mem_array[a] = claripy.If(a == key, b, self._mem_array[a])

    def load_memory_object(self, addr, size):
        if not isinstance(size, int):
            return

        error = False
        result = claripy.BVV(0x00, 0)
        for i in range(size):
            a = addr + size - i - 1
            b = claripy.BVV(0x00, 8)
            if isinstance(a, int):
                if a in self._mem_array:
                    b = self._mem_array[a]
            else:
                for key in list(self._mem_array.keys()):
                    if not claripy.is_false(a == key):
                        b = claripy.If(a == key, self._mem_array[a], b)
            result = result.concat(b)
        return result

    

class SimSegmentedMemory(SimPagedMemory):
    def __init__(self, segments=None, memory_backer=None, permissions_backer=None, pages=None, initialized=None, name_mapping=None, hash_mapping=None, page_size=None, symbolic_addrs=None, check_permissions=False):
        super(SimSegmentedMemory, self).__init__(memory_backer, permissions_backer, pages, initialized, name_mapping, hash_mapping, page_size, symbolic_addrs, check_permissions)
        self._segments = [] if segments is None else segments

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
            '_segments': self._segments
        }

    def branch(self):
        new_name_mapping = self._name_mapping.new_child() if options.REVERSE_MEMORY_NAME_MAP in self.state.options else self._name_mapping
        new_hash_mapping = self._hash_mapping.new_child() if options.REVERSE_MEMORY_HASH_MAP in self.state.options else self._hash_mapping

        new_pages = dict(self._pages)
        self._cowed = set()
        m = SimSegmentedMemory(memory_backer=self._memory_backer,
                           permissions_backer=self._permissions_backer,
                           pages=new_pages,
                           initialized=set(self._initialized),
                           page_size=self._page_size,
                           name_mapping=new_name_mapping,
                           hash_mapping=new_hash_mapping,
                           symbolic_addrs=dict(self._symbolic_addrs),
                           check_permissions=self._check_perms,
                           segments=copy.deepcopy(self._segments))
        m._preapproved_stack = self._preapproved_stack
        return m


    def my_store_memory_object(self, data, addr, size):
        if not isinstance(size, int):
            return
        
        found = False
        for seg in self._segments:
            if not claripy.is_false(claripy.And(addr >= seg._addr, addr + size <= seg._addr + seg._length)):
                seg.store_memory_object(data, addr, size)
                found = True
        if not found:
            seg = Segment()
            seg.store_memory_object(data, addr, size, init=True)
            self._segments.append(seg)
        l.warn("segmented memory store")

    def my_load_memory_object(self, addr, size):
        if not isinstance(size, int):
            return

        result = claripy.ast.bv.BVV(0x00, size * 8)
        for seg in self._segments:
            c = claripy.And(addr >= seg._addr, addr + size <= seg._addr + seg._length)
            if not claripy.is_false(c):
                mo = seg.load_memory_object(addr, size)
                result = claripy.If(c, mo, result)
        return result

    
