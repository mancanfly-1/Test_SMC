import z3
from libirpy import util
import datatype.datatypes as dt

#specification


def css_scp_off(old, psci_power_state_ARM_PWR_LVL0, psci_power_state_ARM_PWR_LVL1,psci_power_state_ARM_PWR_LVL2,core_pos):
    channel_id = dt.GET_SCMI_CHANNEL_ID(core_pos)
    domain_id = dt.GET_SCMI_DOMAIN_ID(core_pos)
    scmi_mbx_mem_id = old.scmi_channels[channel_id].scmi_mbx_mem_id
    scmi_pwr_state = 0
    scmi_power_state_off = 0
    # validation condition for change scmi_pwr_state
    cond = z3.And(
        # core_pos must less than 15
        core_pos <=15,
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


# An example of channel initialization interface
# old:original state space
# chan_id:channel ID
# flags:
# uuid:UUID
def chan_init(old, chan_id, flags, uuid):
    # conditions parameter must satisfied
    cond = z3.And(
        # range of channel ID 
        z3.And(chan_id >=0, chan_id < dt.NCHANID),
        z3.And(uuid >= 0, uuid <dt.NUUID),
    )
    # get a deep clone of old TIPC state object and named 'new'
    new = old.copy()
    # another condition combine the limitation to parameter 'flags'
    cond2 = z3.And(cond, (flags & dt.IPC_CHAN_FLAG_SERVER != 0))
    # change property of TIPC state object 'new'
    new.channels[chan_id].pathid = dt.NPATHID
    new.channels[chan_id].uuid = uuid
    new.channels[chan_id].port_id = dt.NPORT
    new.channels[chan_id].aux_state = z3.BitVecVal(0,64)
    new.channels[chan_id].ref_count = z3.BitVecVal(0,32) # before 0
    new.channels[chan_id].ipc_msg_queue_id = dt.NMSG_QUEUE
    new.channels[chan_id].peer = dt.NCHANID
    new.channels[chan_id].state = dt.IPC_CHAN_STATE_ACCEPTING
    new.channels[chan_id].flags = flags
    # another TIPC state object and named 'new2'
    new2 = new.copy()
    # change property of TIPC state object 'new2'
    new2.channels[chan_id].state = dt.IPC_CHAN_STATE_CONNECTING
    # return conditon and respond state object
    return cond, util.If(cond, util.If(cond2, new, new2), old)

