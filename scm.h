#define true 1
#define false 0

#define bool int
#define  U_(_x)	(_x##U)
#define  U(_x)	U_(_x)

typedef signed char        int8_t;
typedef short              int16_t;
typedef int                int32_t;
typedef long long          int64_t;
typedef unsigned char      uint8_t;
typedef unsigned short     uint16_t;
typedef unsigned int       uint32_t;
typedef unsigned long long uint64_t;

#define BIT64(n) (UINT64_C(1) << (n))

/* Local power state for power domains in Run state. */
#define ARM_LOCAL_STATE_RUN	U(0)
/* Local power state for retention. Valid only for CPU power domains */
#define ARM_LOCAL_STATE_RET	U(1)
/* Local power state for power-down. Valid for CPU and cluster power domains */
#define ARM_LOCAL_STATE_OFF	U(2)

typedef uint8_t plat_local_state_t;

#define PLAT_MAX_PWR_LVL		U(2)

#define ARM_PWR_LVL0				U(0)
#define ARM_PWR_LVL1				U(1)
#define ARM_PWR_LVL2				U(2)

#define SCMI_PWR_STATE_SET_FLAG_SYNC	0
#define SCMI_PWR_STATE_SET_FLAG_ASYNC	1

/* SCMI Protocol identifiers */
#define SCMI_PWR_DMN_PROTO_ID			0x11
#define SCMI_SYS_PWR_PROTO_ID			0x12
/* The AP core protocol is a CSS platform-specific extension */
#define SCMI_AP_CORE_PROTO_ID			0x90

/* Mandatory messages IDs for all SCMI protocols */
#define SCMI_PROTO_VERSION_MSG			0x0
#define SCMI_PROTO_ATTR_MSG				0x1
#define SCMI_PROTO_MSG_ATTR_MSG			0x2

/* SCMI power domain management protocol message IDs */
#define SCMI_PWR_STATE_SET_MSG			0x4
#define SCMI_PWR_STATE_GET_MSG			0x5

/* SCMI system power management protocol message IDs */
#define SCMI_SYS_PWR_STATE_SET_MSG		0x3
#define SCMI_SYS_PWR_STATE_GET_MSG		0x4

/* SCMI AP core protocol message IDs */
#define SCMI_AP_CORE_RESET_ADDR_SET_MSG		0x3
#define SCMI_AP_CORE_RESET_ADDR_GET_MSG		0x4

/* Helper macros for system power management protocol commands */

/*
 * Macros to describe the bit-fields of the `attribute` of system power domain
 * protocol PROTOCOL_MSG_ATTRIBUTE message.
 */
#define SYS_PWR_ATTR_WARM_RESET_SHIFT		31
#define SCMI_SYS_PWR_WARM_RESET_SUPPORTED	(1U << SYS_PWR_ATTR_WARM_RESET_SHIFT)

#define SYS_PWR_ATTR_SUSPEND_SHIFT		30
#define SCMI_SYS_PWR_SUSPEND_SUPPORTED		(1 << SYS_PWR_ATTR_SUSPEND_SHIFT)

/*
 * Macros to describe the bit-fields of the `flags` parameter of system power
 * domain protocol SYSTEM_POWER_STATE_SET message.
 */
#define SYS_PWR_SET_GRACEFUL_REQ_SHIFT		0
#define SCMI_SYS_PWR_GRACEFUL_REQ		(1 << SYS_PWR_SET_GRACEFUL_REQ_SHIFT)
#define SCMI_SYS_PWR_FORCEFUL_REQ		(0 << SYS_PWR_SET_GRACEFUL_REQ_SHIFT)

/*
 * Macros to describe the `system_state` parameter of system power
 * domain protocol SYSTEM_POWER_STATE_SET message.
 */
#define SCMI_SYS_PWR_SHUTDOWN			0x0
#define SCMI_SYS_PWR_COLD_RESET			0x1
#define SCMI_SYS_PWR_WARM_RESET			0x2
#define SCMI_SYS_PWR_POWER_UP			0x3
#define SCMI_SYS_PWR_SUSPEND			0x4

/*
 * Macros to describe the bit-fields of the `attribute` of AP core protocol
 * AP_CORE_RESET_ADDR set/get messages.
 */
#define SCMI_AP_CORE_LOCK_ATTR_SHIFT		0x0
#define SCMI_AP_CORE_LOCK_ATTR			(1U << SCMI_AP_CORE_LOCK_ATTR_SHIFT)

/* SCMI Error code definitions */
#define SCMI_E_QUEUED			1
#define SCMI_E_SUCCESS			0
#define SCMI_E_NOT_SUPPORTED		-1
#define SCMI_E_INVALID_PARAM		-2
#define SCMI_E_DENIED			-3
#define SCMI_E_NOT_FOUND		-4
#define SCMI_E_OUT_OF_RANGE		-5
#define SCMI_E_BUSY			-6

#define SCMI_PWR_STATE_SET_MSG_LEN		16

/* SCMI mailbox flags */
#define SCMI_FLAG_RESP_POLL	0
#define SCMI_FLAG_RESP_INT	1

#define SCMI_PWR_STATE_SET_MSG_LEN		16
#define SCMI_PWR_STATE_SET_RESP_LEN		8

/* SCMI Channel Status bit fields */
#define SCMI_CH_STATUS_RES0_MASK	0xFFFFFFFE
#define SCMI_CH_STATUS_FREE_SHIFT	0
#define SCMI_CH_STATUS_FREE_WIDTH	1
#define SCMI_CH_STATUS_FREE_MASK	((1 << SCMI_CH_STATUS_FREE_WIDTH) - 1)

#define SCMI_MSG_TOKEN_SHIFT		18
#define SCMI_MSG_TOKEN_WIDTH		10
#define SCMI_MSG_TOKEN_MASK		((1 << SCMI_MSG_TOKEN_WIDTH) - 1)

/* SCMI message header format bit field */
#define SCMI_MSG_ID_SHIFT		0
#define SCMI_MSG_ID_WIDTH		8
#define SCMI_MSG_ID_MASK		((1 << SCMI_MSG_ID_WIDTH) - 1)

#define SCMI_MSG_PROTO_ID_SHIFT		10
#define SCMI_MSG_PROTO_ID_WIDTH		8
#define SCMI_MSG_PROTO_ID_MASK		((1 << SCMI_MSG_PROTO_ID_WIDTH) - 1)

#define SCMI_PWR_STATE_LVL_WIDTH		4
#define SCMI_PWR_STATE_MAX_PWR_LVL_SHIFT	16
#define SCMI_PWR_STATE_MAX_PWR_LVL_WIDTH	4
#define SCMI_PWR_STATE_MAX_PWR_LVL_MASK		\
				((1 << SCMI_PWR_STATE_MAX_PWR_LVL_WIDTH) - 1)

#define SCMI_PWR_STATE_LVL_MASK			\
				((1 << SCMI_PWR_STATE_LVL_WIDTH) - 1)

#define SCMI_IS_CHANNEL_FREE(status)					\
	(!!(((status) >> SCMI_CH_STATUS_FREE_SHIFT) & SCMI_CH_STATUS_FREE_MASK))

#define SCMI_MARK_CHANNEL_BUSY(status)	do {				\
		(status) &= ~(SCMI_CH_STATUS_FREE_MASK <<		\
				SCMI_CH_STATUS_FREE_SHIFT);		\
	} while (0)

#define SET_SCMI_CHANNEL_ID(n)		(((n) & SCMI_CHANNEL_ID_MASK) << \
					 SCMI_CHANNEL_ID_SHIFT)
#define SET_SCMI_DOMAIN_ID(n)		((n) & SCMI_DOMAIN_ID_MASK)
#define GET_SCMI_CHANNEL_ID(n)		(((n) >> SCMI_CHANNEL_ID_SHIFT) & \
					 SCMI_CHANNEL_ID_MASK)
#define GET_SCMI_DOMAIN_ID(n)		((n) & SCMI_DOMAIN_ID_MASK)

#define SCMI_PAYLOAD_RET_VAL1(payld_arr, val1)				\
		(val1) = mmio_read_32((uintptr_t)&payld_arr[0])

#define SCMI_PAYLOAD_ARG3(payld_arr, arg1, arg2, arg3)	do {		\
		SCMI_PAYLOAD_ARG2(payld_arr, arg1, arg2);		\
		mmio_write_32((uintptr_t)&payld_arr[2], arg3);		\
	} while (0)

#define SCMI_MSG_CREATE(_protocol, _msg_id, _token)				\
	((((_protocol) & SCMI_MSG_PROTO_ID_MASK) << SCMI_MSG_PROTO_ID_SHIFT) |	\
	(((_msg_id) & SCMI_MSG_ID_MASK) << SCMI_MSG_ID_SHIFT) |			\
	(((_token) & SCMI_MSG_TOKEN_MASK) << SCMI_MSG_TOKEN_SHIFT))

typedef enum {
	scmi_power_state_off = 0,
	scmi_power_state_on = 1,
	scmi_power_state_sleep = 2,
} scmi_power_state_t;

typedef struct psci_power_state {
	/*
	 * The pwr_domain_state[] stores the local power state at each level
	 * for the CPU.
	 */
	plat_local_state_t pwr_domain_state[PLAT_MAX_PWR_LVL + U(1)];
#if PSCI_OS_INIT_MODE
	/*
	 * The highest power level at which the current CPU is the last running
	 * CPU.
	 */
	unsigned int last_at_pwrlvl;
#endif
} psci_power_state_t;

typedef struct psci_power_state_1 {

	/* 
	将数组类型的domain state 改为具体变量，分别代表1级、2级、3级
	*/
	plat_local_state_t pwr_domain_state_lvl1;
	plat_local_state_t pwr_domain_state_lvl2;
	plat_local_state_t pwr_domain_state_lvl3;
	unsigned int last_at_pwrlvl;

} psci_power_state_1_t;


typedef struct mailbox_mem {
	uint32_t res_a; /* Reserved */
	volatile uint32_t status;
	uint64_t res_b; /* Reserved */
	uint32_t flags;
	volatile uint32_t len;
	volatile uint32_t msg_header;
	uint32_t payload[];
} mailbox_mem_t;

/*
 * Structure to represent an SCMI channel.
 */
typedef struct scmi_channel {
	/* SCMI mailbox memory */
	uint32_t scmi_mbx_mem_id;
	/* The door bell register address */
	uintptr_t db_reg_addr;
	/* The bit mask that need to be preserved when ringing doorbell */
	uint32_t db_preserve_mask;
	/* The bit mask that need to be set to ring doorbell */
	uint32_t db_modify_mask;
	/* The handler for ringing doorbell */
	//void (*ring_doorbell)(struct scmi_channel_plat_info *plat_info);
	/* cookie is unused now. But added for future enhancements. */
	// void *cookie;
	 /* The lock for channel access */
	//scmi_lock_t *lock;
	/* Indicate whether the channel is initialized */
	int is_initialized;
} scmi_channel_t;


static inline void validate_scmi_channel(scmi_channel_t *ch)
{
	// assert(ch && ch->is_initialized);
	// assert(ch->info && ch->info->scmi_mbx_mem);
}

static inline unsigned int css_system_pwr_state(const psci_power_state_t *state)
{
#if (PLAT_MAX_PWR_LVL == CSS_SYSTEM_PWR_DMN_LVL)
	return state->pwr_domain_state[CSS_SYSTEM_PWR_DMN_LVL];
#else
	return 0;
#endif
}


