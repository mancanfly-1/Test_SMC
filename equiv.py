import z3
from libirpy import util
import datatype.datatypes as dt

def is_channel_valid(chan_id):
    return z3.And(chan_id >=0, chan_id <dt.PLAT_ARM_SCMI_CHANNEL_COUNT)

def is_scmi_mbx_mem_id_valid(scmi_mbx_mem_id):
    print(dt.PLAT_ARM_SCMI_MAILBOX_COUNT.sort())
    return z3.And(scmi_mbx_mem_id >=0, z3.ULT(scmi_mbx_mem_id, dt.PLAT_ARM_SCMI_MAILBOX_COUNT))

def channel_field_equiv(conj,chan_id,ctx, SCMstate,field_name):
    #print(field_name)
    conj.append(z3.ForAll([chan_id], z3.Implies(is_channel_valid(chan_id),
        util.global_field_element(ctx, '@scmi_channels', field_name, chan_id) ==
        getattr(SCMstate.scmi_channels[chan_id], field_name))))

def mailbox_mem_field_equiv(conj,mailbox_mem_id,ctx, SCMstate,field_name):
    conj.append(z3.ForAll([mailbox_mem_id], z3.Implies(is_scmi_mbx_mem_id_valid(mailbox_mem_id),
        util.global_field_element(ctx, '@mailbox_mem_table', field_name, mailbox_mem_id) ==
        getattr(SCMstate.mailbox_mems[mailbox_mem_id], field_name))))
def mailbox_mem_equiv(conj,ctx, SCMstate):
    scmi_mbx_mem_id= util.FreshBitVec('scmi_mbx_mem_id',dt.mailbox_id)
    mailbox_mem_field_equiv(conj,scmi_mbx_mem_id,ctx,SCMstate,'res_a')
    mailbox_mem_field_equiv(conj,scmi_mbx_mem_id,ctx,SCMstate,'status')
    mailbox_mem_field_equiv(conj,scmi_mbx_mem_id,ctx,SCMstate,'res_b')
    mailbox_mem_field_equiv(conj,scmi_mbx_mem_id,ctx,SCMstate,'flags')
    mailbox_mem_field_equiv(conj,scmi_mbx_mem_id,ctx,SCMstate,'len')
    mailbox_mem_field_equiv(conj,scmi_mbx_mem_id,ctx,SCMstate,'msg_header')
    # mailbox_mem_field_equiv(conj,scmi_mbx_mem_id,ctx,SCMstate,'payload')
    scmi_mbx_mem_n = util.FreshBitVec('scmi_mbx_mem_n', dt.mailbox_id)
    idx = util.FreshBitVec('payload_index', 64)
    conj.append(z3.ForAll([scmi_mbx_mem_n, idx], z3.Implies(
        z3.And(
            z3.ULT(scmi_mbx_mem_n, 16),
            z3.ULT(idx, 3)),
        util.global_field_element(ctx, '@mailbox_mem_table','payload',scmi_mbx_mem_n, idx) ==
        SCMstate.mailbox_mems[scmi_mbx_mem_n].payload(idx))))


def channel_equiv(conj, ctx, SCMstate):
    chan_id = util.FreshBitVec('chan_id', dt.chan_id)
    channel_field_equiv(conj,chan_id,ctx,SCMstate,'scmi_mbx_mem_id')
    channel_field_equiv(conj,chan_id,ctx,SCMstate,'db_reg_addr')
    channel_field_equiv(conj,chan_id,ctx,SCMstate,'db_preserve_mask')
    channel_field_equiv(conj,chan_id,ctx,SCMstate,'db_modify_mask')

    conj.append(z3.ForAll([chan_id], z3.Implies(is_channel_valid(chan_id),
        (util.global_field_element(ctx, '@scmi_channels', 'is_initialized', chan_id) != 0) ==
        SCMstate.scmi_channels[chan_id].is_initialized)))


def is_core_pos_valid(core_pos_id):
    return z3.And(core_pos_id >= 0, core_pos_id < z3.BitVecVal(8,32))

def state_equiv(ctx, state):
    conj = []
    #ipc_port_equiv(conj,ctx, state)
    mailbox_mem_equiv(conj,ctx, state)
    channel_equiv(conj,ctx, state)

    # core_pos = util.FreshBitVec('core_pos_id', z3.BitVecSort(64))
    # some problem.
    # conj.append(z3.ForAll([core_pos],z3.Implies(is_core_pos_valid(core_pos),
    # util.global_to_uf_dict(ctx, '@plat_css_core_pos_to_scmi_dmn_id_map')[()](util.i64(0), z3.ZeroExt(64 - core_pos.size(), core_pos)) ==
    #     state.plat_css_core_pos_to_scmi_dmn_id_map[core_pos]))
    #     )
    # conj.append(ctx.globals['#iotlbinv'] == kernelstate.iotlbinv)
    #conj.append(state.ipc_port_table_ptr_to_int == util.global_ptr_to_int(ctx, '@port_table'))
    # conj.append(state.startup_port_table_ptr_to_int == util.global_ptr_to_int(ctx, '@startup_port_table'))
    return z3.And(*conj)