import z3
from libirpy import util
import datatype.datatypes as dt

#specification


def css_scp_off(old, psci_power_state_ARM_PWR_LVL0, psci_power_state_ARM_PWR_LVL1,psci_power_state_ARM_PWR_LVL2,core_pos):
    # validation condition for TIPC interface arguments
    cond = z3.And(
        # ipc_port_id is in [0, NPORT), => z3.And(ipc_port_id >= 0, ipc_port_id < dt.NPORT)
        core_pos >15,
        # server id must a valid uuid format
        z3.Not(GET_SCMI_CHANNEL_ID(core_pos)),
        # path id must a valid path formt =>z3.And(pid >= 0, pid < dt.NPATHID)
        z3.Not(GET_SCMI_DOMAIN_ID(core_pos)), 
        # 
        z3.And(num_recv_bufs > 0, num_recv_bufs < dt.IPC_CHAN_MAX_BUFS),
    )
    new = old.copy()
    new.ipcports[ipc_port_id].uuid = sid
    new.ipcports[ipc_port_id].num_recv_bufs = num_recv_bufs
    new.ipcports[ipc_port_id].state = dt.IPC_PORT_STATE_INVALID
    new.ipcports[ipc_port_id].pathid = pid
    new.ipcports[ipc_port_id].flags = flags
    new.ipcports[ipc_port_id].created = z3.BoolVal(True)
    new.ipcports[ipc_port_id].published = z3.BoolVal(False)
    new.ipcports[ipc_port_id].startup_port = z3.BoolVal(False)
    return cond, util.If(cond, new, old)


def ipc_startup_port_register(old, app_id, pid, flags, startup_port_id):
    cond = z3.And(
        z3.And(app_id>=0, app_id < dt.NAPP),
        z3.And(pid >=0, pid < dt.NPATHID),
        # z3.Not(old.startup_ports[pid].state == z3.BitVecVal(1,z3.BitVecSort(32))),
        z3.And(startup_port_id < dt.NSTARTUPPORT, startup_port_id>=0),
    )

    new = old.copy()
    new.startup_ports[startup_port_id].pid = pid
    new.startup_ports[startup_port_id].app_id = app_id
    new.startup_ports[startup_port_id].flags = flags
    # new.startup_ports[startup_port_id].state = 0
    return cond, util.If(cond, new, old)

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

