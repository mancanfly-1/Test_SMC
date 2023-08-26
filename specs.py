import z3
from libirpy import util
import datatype.datatypes as dt

#specification


def css_scp_off(old, psci_power_state_ARM_PWR_LVL0, psci_power_state_ARM_PWR_LVL1,psci_power_state_ARM_PWR_LVL2,channel_id,domain_id):
    # channel_id = dt.GET_SCMI_CHANNEL_ID(dt.plat_css_core_pos_to_scmi_dmn_id_map[core_pos])
    # domain_id = dt.GET_SCMI_DOMAIN_ID(dt.plat_css_core_pos_to_scmi_dmn_id_map(core_pos))
    scmi_mbx_mem_id = old.scmi_channels[channel_id].scmi_mbx_mem_id
    scmi_pwr_state = 0
    scmi_power_state_off = 0
    # validation condition for change scmi_pwr_state
    cond = z3.And(
        # core_pos must less than 8
        core_pos < 8,
        # channel id must equal to zero
        channel_id == 0,
        # domain_id must equal to zero
        domain_id == 0, 
        # channel must be initialized
        z3.Not(old.scmi_channels[channel_id].is_initialized == 0),
        # mailbox memeory id of channel must less than 15, we define 15 as the biggest mailbox memory array id
        old.scmi_channels[channel_id].scmi_mbx_mem_id <=15,
        # state of mailbox in current channel must free
        z3.Not(dt.SCMI_IS_CHANNEL_FREE(old.mailbox_mem_table[old.scmi_channels[channel_id].scmi_mbx_mem_id]== 0)),
    )

    new = old.copy()
    new.mailbox_mems[scmi_mbx_mem_id].msg_header = dt.SCMI_MSG_CREATE(dt.SCMI_PWR_DMN_PROTO_ID,
			dt.SCMI_PWR_STATE_SET_MSG, 0)
    new.mailbox_mems[scmi_mbx_mem_id].len = dt.SCMI_PWR_STATE_SET_MSG_LEN
    new.mailbox_mems[scmi_mbx_mem_id].flags = dt.SCMI_FLAG_RESP_POLL
    new.mailbox_mems[scmi_mbx_mem_id].payload[0] = dt.SCMI_PWR_STATE_SET_FLAG_ASYNC
    new.mailbox_mems[scmi_mbx_mem_id].payload[1] = domain_id
    new.mailbox_mems[scmi_mbx_mem_id].payload[2] = scmi_pwr_state

    cond1 = z3.And(cond, z3.And(
        z3.Not(psci_power_state_ARM_PWR_LVL0 == dt.ARM_LOCAL_STATE_OFF),
        z3.Not(psci_power_state_ARM_PWR_LVL1 == dt.ARM_LOCAL_STATE_OFF),
        z3.Not(psci_power_state_ARM_PWR_LVL2 == dt.ARM_LOCAL_STATE_OFF),
    ))
    
    cond2 = z3.And(cond, z3.And(
        z3.Not(psci_power_state_ARM_PWR_LVL0 == dt.ARM_LOCAL_STATE_RUN),
        psci_power_state_ARM_PWR_LVL1 == dt.ARM_LOCAL_STATE_RUN,
    ))
    cond3 = z3.And(cond, z3.And(
        z3.Not(psci_power_state_ARM_PWR_LVL0 == dt.ARM_LOCAL_STATE_OFF),
        z3.Not(psci_power_state_ARM_PWR_LVL1 == dt.ARM_LOCAL_STATE_OFF),
        psci_power_state_ARM_PWR_LVL2 == dt.ARM_LOCAL_STATE_OFF,
    ))

    scmi_pwr_state_1 = 0
    dt.SCMI_SET_PWR_STATE_LVL(scmi_pwr_state_1, 0,scmi_power_state_off)
    dt.SCMI_SET_PWR_STATE_LVL(scmi_pwr_state_1, 1,scmi_power_state_off)
    dt.SCMI_SET_PWR_STATE_LVL(scmi_pwr_state_1, 2,scmi_power_state_off)
    dt.SCMI_SET_PWR_STATE_MAX_PWR_LVL(scmi_pwr_state_1, 2)
    new1 = new.copy()
    new1.mailbox_mems[scmi_mbx_mem_id].payload[2] = scmi_pwr_state_1

    scmi_pwr_state_2 = 0
    dt.SCMI_SET_PWR_STATE_LVL(scmi_pwr_state_2, 0, scmi_power_state_off)
    dt.SCMI_SET_PWR_STATE_MAX_PWR_LVL(scmi_pwr_state_2, 0)

    new2 = new.copy()
    new2.mailbox_mems[scmi_mbx_mem_id].payload[2] = scmi_pwr_state_2

    scmi_pwr_state_3 = 0
    dt.SCMI_SET_PWR_STATE_LVL(scmi_pwr_state_3, 0, scmi_power_state_off)
    dt.SCMI_SET_PWR_STATE_LVL(scmi_pwr_state_3, 1, scmi_power_state_off)
    dt.SCMI_SET_PWR_STATE_MAX_PWR_LVL(scmi_pwr_state_3, 1)

    new3 = new.copy()
    new3.mailbox_mems[scmi_mbx_mem_id].payload[2] = scmi_pwr_state_3
    
    return cond, util.If(cond, util.If(cond1, new1, util.If(cond2, new2, util.If(cond3, new3, old))), old)


