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
    import TIPC
    TIPC._init_metadata(ctx)
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

mailbox_id = z3.BitVecSort(32)
chan_id = z3.BitVecSort(32)
MAX_UINT = z3.BitVecVal(32,uint64_t)

# Max channel count.
PLAT_ARM_SCMI_CHANNEL_COUNT= z3.BitVecVal(1,uint64_t)
PLAT_ARM_SCMI_MAILBOX_COUNT = z3.BitVecVal(16,uint64_t)
PLAT_ARM_CLUSTER_COUNT = z3.BitVecVal(8,uint64_t)

plat_css_core_pos_to_scmi_dmn_id_map = [
(SET_SCMI_CHANNEL_ID(0x0) | SET_SCMI_DOMAIN_ID(0x0)),
(SET_SCMI_CHANNEL_ID(0x0) | SET_SCMI_DOMAIN_ID(0x1)),
(SET_SCMI_CHANNEL_ID(0x0) | SET_SCMI_DOMAIN_ID(0x2)),
(SET_SCMI_CHANNEL_ID(0x0) | SET_SCMI_DOMAIN_ID(0x3)),
(SET_SCMI_CHANNEL_ID(0x0) | SET_SCMI_DOMAIN_ID(0x4)),
(SET_SCMI_CHANNEL_ID(0x0) | SET_SCMI_DOMAIN_ID(0x5)),
(SET_SCMI_CHANNEL_ID(0x0) | SET_SCMI_DOMAIN_ID(0x6)),
(SET_SCMI_CHANNEL_ID(0x0) | SET_SCMI_DOMAIN_ID(0x7))]

# plat_css_core_pos_to_scmi_dmn_id_map_0 = (SET_SCMI_CHANNEL_ID(0x0) | SET_SCMI_DOMAIN_ID(0x0))
# plat_css_core_pos_to_scmi_dmn_id_map_1 = (SET_SCMI_CHANNEL_ID(0x0) | SET_SCMI_DOMAIN_ID(0x1))
# plat_css_core_pos_to_scmi_dmn_id_map_2 = (SET_SCMI_CHANNEL_ID(0x0) | SET_SCMI_DOMAIN_ID(0x2))
# plat_css_core_pos_to_scmi_dmn_id_map_3 = (SET_SCMI_CHANNEL_ID(0x0) | SET_SCMI_DOMAIN_ID(0x3))
# plat_css_core_pos_to_scmi_dmn_id_map_4 = (SET_SCMI_CHANNEL_ID(0x0) | SET_SCMI_DOMAIN_ID(0x4))
# plat_css_core_pos_to_scmi_dmn_id_map_5 = (SET_SCMI_CHANNEL_ID(0x0) | SET_SCMI_DOMAIN_ID(0x5))
# plat_css_core_pos_to_scmi_dmn_id_map_6 = (SET_SCMI_CHANNEL_ID(0x0) | SET_SCMI_DOMAIN_ID(0x6))
# plat_css_core_pos_to_scmi_dmn_id_map_7 = (SET_SCMI_CHANNEL_ID(0x0) | SET_SCMI_DOMAIN_ID(0x7))



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
    status = Map(uint32_t, uint32_t)
    flags = Map(uint32_t, uint32_t)
    len = Map(uint32_t, uint32_t)
    msg_header = Map(uint32_t, uint32_t)
    payload = Map(uint32_t, uint32_t)

class Scmi_channel(Struct):
    scmi_mbx_mem_id = Map(uint32_t,uint32_t)
    db_reg_addr = Map(uint32_t,uint64_t)
    db_preserve_mask = Map(uint32_t,uint32_t)
    db_modify_mask = Map(uint32_t,uint32_t)
    is_initialized = Map(uint32_t,uint32_t)
    # state = Map(uint64_t,uint64_t)
"""
Global machine state
"""
class IPCState(BaseStruct):
    # core position map to domain id
    plat_css_core_pos_to_scmi_dmn_id_map =Map(uint32_t,uint32_t)
    # instance Mailbox_mem structure spec
    mailbox_mems = Mailbox_mem()
    # instance channel structure spec
    scmi_channels = Scmi_channel()
