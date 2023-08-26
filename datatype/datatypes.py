import sys
# from venv import create
import copy
from head import *
import libirpy
from libirpy import util
from base import BaseStruct, Struct, Map, Refcnt, Refcnt2


def _populate_enums():
    module = sys.modules[__name__]
    ctx = libirpy.newctx()
    import scm
    scm._init_metadata(ctx)
    for k, v in ctx.metadata.items():
        if isinstance(v, tuple) and v[0] == 'DICompositeType':
            if v[1].get('tag') == 'DW_TAG_enumeration_type':
                name = v[1].get('name')
                size = v[1].get('size')
                elements = v[1].get('elements')

                if name is None or size is None or elements is None:
                    continue

                setattr(module, name + '_t', z3.BitVecSort(size))
                enum = {}

                for element in ctx.metadata.get(elements):
                    element = ctx.metadata.get(element)
                    assert element[0] == 'DIEnumerator'
                    element_name = element[1].get('name')
                    element_value = element[1].get('value')
                    enum[element_name] = z3.BitVecVal(element_value, size)

                setattr(module, name, type(name, (), enum))


# These are populated from llvm metadata info
page_type_t = None
file_type_t = None
proc_state_t = None
intremap_state_t = None


# Fetch the enums from the llvm metadata and populate this module with their values
_populate_enums()

def BIT64(bit): return z3.BitVecVal(1 << bit, 64)
def has_bit(v, bit): return (v & bit) != 0

MAX_INT64 = z3.BitVecVal(2 ** 64 - 1, 64)

mailbox_id = z3.BitVecSort(64)
chan_id = z3.BitVecSort(64)
MAX_UINT = z3.BitVecVal(32,uint64_t)

# Max channel count.
PLAT_ARM_SCMI_CHANNEL_COUNT= 1
PLAT_ARM_SCMI_MAILBOX_COUNT = z3.BitVecVal(16,uint64_t)
PLAT_ARM_CLUSTER_COUNT = 8

plat_css_core_pos_to_scmi_dmn_id_map = [
z3.BitVecVal((SET_SCMI_CHANNEL_ID(0x0) | SET_SCMI_DOMAIN_ID(0x0)),uint32_t),
z3.BitVecVal((SET_SCMI_CHANNEL_ID(0x0) | SET_SCMI_DOMAIN_ID(0x1)),uint32_t),
z3.BitVecVal((SET_SCMI_CHANNEL_ID(0x0) | SET_SCMI_DOMAIN_ID(0x2)),uint32_t),
z3.BitVecVal((SET_SCMI_CHANNEL_ID(0x0) | SET_SCMI_DOMAIN_ID(0x3)),uint32_t),
z3.BitVecVal((SET_SCMI_CHANNEL_ID(0x0) | SET_SCMI_DOMAIN_ID(0x4)),uint32_t),
z3.BitVecVal((SET_SCMI_CHANNEL_ID(0x0) | SET_SCMI_DOMAIN_ID(0x5)),uint32_t),
z3.BitVecVal((SET_SCMI_CHANNEL_ID(0x0) | SET_SCMI_DOMAIN_ID(0x6)),uint32_t),
z3.BitVecVal((SET_SCMI_CHANNEL_ID(0x0) | SET_SCMI_DOMAIN_ID(0x7)),uint32_t)]

# IPC_PORT_STATE_INVALID = 0

ERR_INVALID_ARGS = -1
ERR_ALREADY_EXISTS = -2
ERR_NO_MEMORY = -3
ERR_NOT_READY = -4
ERR_NOT_FOUND = -5
ERR_CHANNEL_CLOSED = -6
ERR_INVALID_LEN = -7
ERR_TOO_BIG = -8
    

class Mailbox_mem(Struct):
    res_a = Map(uint64_t, uint32_t)
    status = Map(uint64_t, uint32_t)
    res_b = Map(uint64_t, uint64_t)
    flags = Map(uint64_t, uint32_t)
    len = Map(uint64_t, uint32_t)
    msg_header = Map(uint64_t, uint32_t)
    payload = Map(uint64_t, uint64_t,uint32_t)

class Scmi_channel(Struct):
    scmi_mbx_mem_id = Map(uint64_t,uint64_t)
    db_reg_addr = Map(uint64_t,uint64_t)
    db_preserve_mask = Map(uint64_t,uint32_t)
    db_modify_mask = Map(uint64_t,uint32_t)
    is_initialized = Map(uint64_t,bool_t)
    # state = Map(uint64_t,uint64_t)
"""
Global machine state
"""
class SCMState(BaseStruct):
    # core position map to domain id
    #plat_css_core_pos_to_scmi_dmn_id_map = Map(uint64_t,uint32_t)
    # instance Mailbox_mem structure spec
    mailbox_mems = Mailbox_mem()
    # instance channel structure spec
    scmi_channels = Scmi_channel()
