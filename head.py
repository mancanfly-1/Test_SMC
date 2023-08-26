import z3

bool_t = z3.BoolSort()
size_t = z3.BitVecSort(64)
uint64_t = z3.BitVecSort(64)
uint32_t = z3.BitVecSort(32)
uint16_t = z3.BitVecSort(16)
uint8_t = z3.BitVecSort(8)

int32_t = z3.BitVecSort(32)


SCMI_DOMAIN_ID_MASK = 0xFFFF
SCMI_CHANNEL_ID_MASK = 0xFFFF
SCMI_CHANNEL_ID_SHIFT = 16

# Local power state for power domains in different state. 
ARM_LOCAL_STATE_RUN = z3.BitVecVal(0, uint32_t)
ARM_LOCAL_STATE_RET = z3.BitVecVal(1, uint32_t)
ARM_LOCAL_STATE_OFF = z3.BitVecVal(2, uint32_t)

PLAT_MAX_PWR_LVL = z3.BitVecVal(2, uint32_t)

ARM_PWR_LVL0 = z3.BitVecVal(0, uint32_t)
ARM_PWR_LVL1 = z3.BitVecVal(1, uint32_t)
ARM_PWR_LVL2 = z3.BitVecVal(2, uint32_t)

PLAT_ARM_SCMI_CHANNEL_COUNT= 1
PLAT_ARM_SCMI_MAILBOX_COUNT = z3.BitVecVal(16, uint32_t)
PLAT_ARM_CLUSTER_COUNT = 8

SCMI_PWR_STATE_SET_FLAG_SYNC = z3.BitVecVal(0, uint32_t)
SCMI_PWR_STATE_SET_FLAG_ASYNC = z3.BitVecVal(1, uint32_t)

# SCMI Protocol identifiers
SCMI_PWR_DMN_PROTO_ID = z3.BitVecVal(0x11, uint32_t)
SCMI_SYS_PWR_PROTO_ID = z3.BitVecVal(0x12, uint32_t)

SCMI_AP_CORE_PROTO_ID = z3.BitVecVal(0x90, uint32_t)

SCMI_PROTO_VERSION_MSG = z3.BitVecVal(0, uint32_t)
SCMI_PROTO_ATTR_MSG = z3.BitVecVal(1, uint32_t)
SCMI_PROTO_MSG_ATTR_MSG = z3.BitVecVal(2, uint32_t)

SCMI_PWR_STATE_SET_MSG = z3.BitVecVal(4, uint32_t)
SCMI_PWR_STATE_GET_MSG = z3.BitVecVal(5, uint32_t)

SCMI_SYS_PWR_STATE_SET_MSG = z3.BitVecVal(3, uint32_t)
SCMI_SYS_PWR_STATE_GET_MSG = z3.BitVecVal(4, uint32_t)

SCMI_AP_CORE_RESET_ADDR_SET_MSG = z3.BitVecVal(3, uint32_t)
SCMI_AP_CORE_RESET_ADDR_GET_MSG = z3.BitVecVal(4, uint32_t)

# /*
#  * Macros to describe the bit-fields of the `attribute` of system power domain
#  * protocol PROTOCOL_MSG_ATTRIBUTE message.
#  */
SYS_PWR_ATTR_WARM_RESET_SHIFT = z3.BitVecVal(31, uint32_t)
SCMI_SYS_PWR_WARM_RESET_SUPPORTED = z3.BitVecVal(1, uint32_t) << SYS_PWR_ATTR_WARM_RESET_SHIFT

SYS_PWR_ATTR_WARM_RESET_SHIFT = z3.BitVecVal(30, uint32_t)
SCMI_SYS_PWR_SUSPEND_SUPPORTED = z3.BitVecVal(1, uint32_t) << SYS_PWR_ATTR_WARM_RESET_SHIFT


# /*
#  * Macros to describe the bit-fields of the `flags` parameter of system power
#  * domain protocol SYSTEM_POWER_STATE_SET message.
#  */
SYS_PWR_SET_GRACEFUL_REQ_SHIFT = z3.BitVecVal(0, uint32_t)
SCMI_SYS_PWR_GRACEFUL_REQ = (z3.BitVecVal(1, uint32_t) << SYS_PWR_SET_GRACEFUL_REQ_SHIFT)
SCMI_SYS_PWR_FORCEFUL_REQ = (z3.BitVecVal(0, uint32_t) << SYS_PWR_SET_GRACEFUL_REQ_SHIFT)

SCMI_SYS_PWR_SHUTDOWN = z3.BitVecVal(0, uint32_t)
SCMI_SYS_PWR_COLD_RESET = z3.BitVecVal(1, uint32_t)
SCMI_SYS_PWR_WARM_RESET = z3.BitVecVal(2, uint32_t)
SCMI_SYS_PWR_POWER_UP = z3.BitVecVal(3, uint32_t)
SCMI_SYS_PWR_SUSPEND = z3.BitVecVal(4, uint32_t)

# /*
#  * Macros to describe the bit-fields of the `attribute` of AP core protocol
#  * AP_CORE_RESET_ADDR set/get messages.
#  */

SCMI_AP_CORE_LOCK_ATTR_SHIFT = z3.BitVecVal(0, uint32_t)
SCMI_AP_CORE_LOCK_ATTR = (z3.BitVecVal(0, uint32_t) << SCMI_AP_CORE_LOCK_ATTR_SHIFT)

SCMI_E_QUEUED = 1
SCMI_E_SUCCESS = 0
SCMI_E_NOT_SUPPORTED = -1
SCMI_E_INVALID_PARAM = -2
SCMI_E_DENIED = -3
SCMI_E_NOT_FOUND = -4
SCMI_E_OUT_OF_RANGE = -5
SCMI_E_BUSY = -6

SCMI_PWR_STATE_SET_MSG_LEN = z3.BitVecVal(16, uint32_t)

SCMI_FLAG_RESP_POLL = z3.BitVecVal(0, uint32_t)
SCMI_FLAG_RESP_INT = z3.BitVecVal(1, uint32_t)

SCMI_PWR_STATE_SET_MSG_LEN = z3.BitVecVal(16, uint32_t)
SCMI_PWR_STATE_SET_RESP_LEN = z3.BitVecVal(8, uint32_t)

SCMI_CH_STATUS_RES0_MASK = z3.BitVecVal(0xFFFFFFFE, uint32_t)
SCMI_CH_STATUS_FREE_SHIFT = z3.BitVecVal(0, uint32_t)
SCMI_CH_STATUS_FREE_WIDTH = z3.BitVecVal(2, uint32_t)
SCMI_CH_STATUS_FREE_MASK = z3.BitVecVal(1, uint32_t) << SCMI_CH_STATUS_FREE_WIDTH - z3.BitVecVal(1, uint32_t)

SCMI_MSG_TOKEN_SHIFT = z3.BitVecVal(18, uint32_t)
SCMI_MSG_TOKEN_WIDTH =  z3.BitVecVal(10, uint32_t)
SCMI_MSG_TOKEN_MASK =  (z3.BitVecVal(1, uint32_t) << SCMI_MSG_TOKEN_WIDTH) - z3.BitVecVal(1, uint32_t)

# SCMI message header format bit field
SCMI_MSG_ID_SHIFT = z3.BitVecVal(0, uint32_t)
SCMI_MSG_ID_WIDTH =  z3.BitVecVal(8, uint32_t)
SCMI_MSG_ID_MASK =  (z3.BitVecVal(1, uint32_t) << SCMI_MSG_ID_WIDTH) - z3.BitVecVal(1, uint32_t)

SCMI_MSG_PROTO_ID_SHIFT = z3.BitVecVal(10, uint32_t)
SCMI_MSG_PROTO_ID_WIDTH =  z3.BitVecVal(8, uint32_t)
SCMI_MSG_PROTO_ID_MASK =  (z3.BitVecVal(1, uint32_t) << SCMI_MSG_PROTO_ID_WIDTH) - z3.BitVecVal(1, uint32_t)

SCMI_PWR_STATE_LVL_WIDTH = z3.BitVecVal(4, uint32_t)
SCMI_PWR_STATE_MAX_PWR_LVL_SHIFT = z3.BitVecVal(16, uint32_t)
SCMI_PWR_STATE_MAX_PWR_LVL_WIDTH = z3.BitVecVal(4, uint32_t)
SCMI_PWR_STATE_MAX_PWR_LVL_MASK = (z3.BitVecVal(1, uint32_t) << SCMI_PWR_STATE_MAX_PWR_LVL_WIDTH) - z3.BitVecVal(1, uint32_t)

SCMI_PWR_STATE_LVL_MASK = (z3.BitVecVal(1, uint32_t) << SCMI_PWR_STATE_LVL_WIDTH) - z3.BitVecVal(1, uint32_t)

def SCMI_IS_CHANNEL_FREE(status):
    # (!!(((status) >> SCMI_CH_STATUS_FREE_SHIFT) & SCMI_CH_STATUS_FREE_MASK)) why two negitve
    return ((((status) >> SCMI_CH_STATUS_FREE_SHIFT) & SCMI_CH_STATUS_FREE_MASK))

def SET_SCMI_CHANNEL_ID(n):
    return (((n) & SCMI_CHANNEL_ID_MASK) << SCMI_CHANNEL_ID_SHIFT)

def SET_SCMI_DOMAIN_ID(n):
    return ((n) & SCMI_DOMAIN_ID_MASK)

def GET_SCMI_CHANNEL_ID(n):
    return (((n) >> SCMI_CHANNEL_ID_SHIFT) & SCMI_CHANNEL_ID_MASK)

def GET_SCMI_DOMAIN_ID(n):
    return ((n) & SCMI_DOMAIN_ID_MASK)

def SCMI_MSG_CREATE(_protocol, _msg_id, _token):
    return ((((_protocol) & SCMI_MSG_PROTO_ID_MASK) << SCMI_MSG_PROTO_ID_SHIFT) |
    (((_msg_id) & SCMI_MSG_ID_MASK) << SCMI_MSG_ID_SHIFT) |	
    (((_token) & SCMI_MSG_TOKEN_MASK) << SCMI_MSG_TOKEN_SHIFT))
