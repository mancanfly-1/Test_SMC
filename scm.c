#include <stdio.h>
#include <limits.h>
#include <string.h>
#include "scm.h"

#define SCMI_E_QUEUED			1
#define SCMI_E_SUCCESS			0
#define SCMI_E_NOT_SUPPORTED		-1
#define SCMI_E_INVALID_PARAM		-2
#define SCMI_E_DENIED			-3
#define SCMI_E_NOT_FOUND		-4
#define SCMI_E_OUT_OF_RANGE		-5
#define SCMI_E_BUSY			-6
#define NMAIL				16
#define SCMI_DOMAIN_ID_MASK		U(0xFFFF)
#define SCMI_CHANNEL_ID_MASK		U(0xFFFF)
#define SCMI_CHANNEL_ID_SHIFT		U(16)

#define SCMI_SET_PWR_STATE_MAX_PWR_LVL(_power_state, _max_level)		\
		(_power_state) |= ((_max_level) & SCMI_PWR_STATE_MAX_PWR_LVL_MASK)\
				<< SCMI_PWR_STATE_MAX_PWR_LVL_SHIFT

#define SCMI_SET_PWR_STATE_LVL(_power_state, _level, _level_state)		\
		(_power_state) |= ((_level_state) & SCMI_PWR_STATE_LVL_MASK)	\
				<< (SCMI_PWR_STATE_LVL_WIDTH * (_level))

#define SET_SCMI_CHANNEL_ID(n)		(((n) & SCMI_CHANNEL_ID_MASK) << \
					 SCMI_CHANNEL_ID_SHIFT)

#define SET_SCMI_DOMAIN_ID(n)		((n) & SCMI_DOMAIN_ID_MASK)

#define PLAT_ARM_SCMI_CHANNEL_COUNT	1

const uint32_t plat_css_core_pos_to_scmi_dmn_id_map[] = {
	(SET_SCMI_CHANNEL_ID(0x0) | SET_SCMI_DOMAIN_ID(0x0)),
	(SET_SCMI_CHANNEL_ID(0x0) | SET_SCMI_DOMAIN_ID(0x1)),
	(SET_SCMI_CHANNEL_ID(0x0) | SET_SCMI_DOMAIN_ID(0x2)),
	(SET_SCMI_CHANNEL_ID(0x0) | SET_SCMI_DOMAIN_ID(0x3)),
	(SET_SCMI_CHANNEL_ID(0x0) | SET_SCMI_DOMAIN_ID(0x4)),
	(SET_SCMI_CHANNEL_ID(0x0) | SET_SCMI_DOMAIN_ID(0x5)),
	(SET_SCMI_CHANNEL_ID(0x0) | SET_SCMI_DOMAIN_ID(0x6)),
	(SET_SCMI_CHANNEL_ID(0x0) | SET_SCMI_DOMAIN_ID(0x7)),
#if (PLAT_ARM_CLUSTER_COUNT > 8)
	(SET_SCMI_CHANNEL_ID(0x0) | SET_SCMI_DOMAIN_ID(0x8)),
	(SET_SCMI_CHANNEL_ID(0x0) | SET_SCMI_DOMAIN_ID(0x9)),
	(SET_SCMI_CHANNEL_ID(0x0) | SET_SCMI_DOMAIN_ID(0xA)),
	(SET_SCMI_CHANNEL_ID(0x0) | SET_SCMI_DOMAIN_ID(0xB)),
	(SET_SCMI_CHANNEL_ID(0x0) | SET_SCMI_DOMAIN_ID(0xC)),
	(SET_SCMI_CHANNEL_ID(0x0) | SET_SCMI_DOMAIN_ID(0xD)),
	(SET_SCMI_CHANNEL_ID(0x0) | SET_SCMI_DOMAIN_ID(0xE)),
	(SET_SCMI_CHANNEL_ID(0x0) | SET_SCMI_DOMAIN_ID(0xF)),
#endif
};



/*
 * The global handles for invoking the SCMI driver APIs after the driver
 * has been initialized.
 */
// static void *scmi_handles[PLAT_ARM_SCMI_CHANNEL_COUNT];

/* The global SCMI channels array */
static scmi_channel_t scmi_channels[PLAT_ARM_SCMI_CHANNEL_COUNT];

static mailbox_mem_t mailbox_mem_table[NMAIL];


// static void css_scp_core_pos_to_scmi_channel(unsigned int core_pos,
// 		unsigned int *scmi_domain_id, unsigned int *scmi_channel_id)
// {
// 	unsigned int composite_id;

// 	composite_id = plat_css_core_pos_to_scmi_dmn_id_map[core_pos];

// 	*scmi_channel_id = GET_SCMI_CHANNEL_ID(composite_id);
// 	*scmi_domain_id = GET_SCMI_DOMAIN_ID(composite_id);
// }

static inline unsigned int get_scmi_channel_id(unsigned int core_pos)
{
	return GET_SCMI_CHANNEL_ID(plat_css_core_pos_to_scmi_dmn_id_map[core_pos]);
}

static inline unsigned int get_scmi_domain_id(unsigned int core_pos)
{
	return GET_SCMI_DOMAIN_ID(plat_css_core_pos_to_scmi_dmn_id_map[core_pos]);
}

int get_composite_id(unsigned int core_pos)
{
	return plat_css_core_pos_to_scmi_dmn_id_map[core_pos];
}

/*
 * API to set the SCMI power domain power state.
 */
int scmi_pwr_state_set(void *p, uint32_t domain_id,
					uint32_t scmi_pwr_state)
{
	// mailbox_mem_t *mbx_mem;
	// unsigned int token = 0;
	// int ret;

	// /*
	//  * Only asynchronous mode of `set power state` command is allowed on
	//  * application processors.
	//  */
	// uint32_t pwr_state_set_msg_flag = SCMI_PWR_STATE_SET_FLAG_ASYNC;
	// scmi_channel_t *ch = (scmi_channel_t *)p;

	// validate_scmi_channel(ch);
	// // 使用ch时,先设置锁.
	// scmi_get_channel(ch);

	// //mbx_mem = (mailbox_mem_t *)(ch->info->scmi_mbx_mem);
	// mbx_mem->msg_header = SCMI_MSG_CREATE(SCMI_PWR_DMN_PROTO_ID,
	// 		SCMI_PWR_STATE_SET_MSG, token);
	// mbx_mem->len = SCMI_PWR_STATE_SET_MSG_LEN;
	// mbx_mem->flags = SCMI_FLAG_RESP_POLL;
	// // 该define是一个do while函数,如何处理
	// SCMI_PAYLOAD_ARG3(mbx_mem->payload, pwr_state_set_msg_flag,
	// 					domain_id, scmi_pwr_state);

	// scmi_send_sync_command(ch);

	// /* Get the return values */
	// SCMI_PAYLOAD_RET_VAL1(mbx_mem->payload, ret);
	// assert(mbx_mem->len == SCMI_PWR_STATE_SET_RESP_LEN);
	// assert(token == SCMI_MSG_GET_TOKEN(mbx_mem->msg_header));

	// scmi_put_channel(ch);
	return 0;
	//return ret;
}

/*
 * Helper function to turn off a CPU power domain and its parent power domains
 * if applicable.
 */
/*
 * 参数psci_power_state 静态资源管理,使用数组保存该state,或者将state分解为3个参数
 * psci_power_state_ARM_PWR_LVL0;
 * psci_power_state_ARM_PWR_LVL1;
 * psci_power_state_ARM_PWR_LVL2.
*/
// void css_scp_off(const struct psci_power_state *target_state)
// {
// 	unsigned int lvl = 0, channel_id, domain_id;
// 	int ret;
// 	uint32_t scmi_pwr_state = 0;

// 	/* At-least the CPU level should be specified to be OFF */
// 	// assert(target_state->pwr_domain_state[ARM_PWR_LVL0] ==
// 	// 						ARM_LOCAL_STATE_OFF);

// 	/* PSCI CPU OFF cannot be used to turn OFF system power domain */
// 	// assert(css_system_pwr_state(target_state) == ARM_LOCAL_STATE_RUN);

// 	for (; lvl <= PLAT_MAX_PWR_LVL; lvl++) {
// 		if (target_state->pwr_domain_state[lvl] == ARM_LOCAL_STATE_RUN)
// 			break;

// 		// assert(target_state->pwr_domain_state[lvl] == ARM_LOCAL_STATE_OFF);
// 		SCMI_SET_PWR_STATE_LVL(scmi_pwr_state, lvl,
// 				scmi_power_state_off);
// 	}


// 	// 从这里开始向下是第二个函数
// 	SCMI_SET_PWR_STATE_MAX_PWR_LVL(scmi_pwr_state, lvl - 1);

// 	// 可以直接拆开函数
// 	// plat_my_core_pos()返回 unsigned int,该值的范围是0-7之间
// 	css_scp_core_pos_to_scmi_channel(0,
// 			&domain_id, &channel_id);
// 	// scmi_handles数组的大小为1，这里需要修改。
// 	ret = scmi_pwr_state_set(scmi_channels[channel_id],
// 		domain_id, scmi_pwr_state);
// 	if (ret != SCMI_E_QUEUED && ret != SCMI_E_SUCCESS) {
// 		//ERROR("SCMI set power state command return 0x%x unexpected\n", ret);
// 		//panic();
// 	}
// }

int get_pwr_state(plat_local_state_t psci_power_state_ARM_PWR_LVL0, plat_local_state_t psci_power_state_ARM_PWR_LVL1,plat_local_state_t psci_power_state_ARM_PWR_LVL2)
{

	uint32_t scmi_pwr_state = 0;

	/* At-least the CPU level should be specified to be OFF */
	// assert(target_state->pwr_domain_state[ARM_PWR_LVL0] ==
	// 						ARM_LOCAL_STATE_OFF);
	// 与下面的for语句进行呼应
	if(psci_power_state_ARM_PWR_LVL0 == ARM_LOCAL_STATE_OFF || psci_power_state_ARM_PWR_LVL1 == ARM_LOCAL_STATE_OFF ||
	psci_power_state_ARM_PWR_LVL2 == ARM_LOCAL_STATE_OFF)
	{
		return -1;
	}
	/* PSCI power state是否还有其他的state? */

	if(psci_power_state_ARM_PWR_LVL0 != ARM_LOCAL_STATE_RUN &&
		psci_power_state_ARM_PWR_LVL1 != ARM_LOCAL_STATE_RUN &&
		psci_power_state_ARM_PWR_LVL2 != ARM_LOCAL_STATE_RUN)
	{
		SCMI_SET_PWR_STATE_LVL(scmi_pwr_state, 0,
			scmi_power_state_off);
		SCMI_SET_PWR_STATE_LVL(scmi_pwr_state, 1,
			scmi_power_state_off);
		SCMI_SET_PWR_STATE_LVL(scmi_pwr_state, 2,
			scmi_power_state_off);
		SCMI_SET_PWR_STATE_MAX_PWR_LVL(scmi_pwr_state, 2);
	}

	if(psci_power_state_ARM_PWR_LVL0 != ARM_LOCAL_STATE_RUN &&
		psci_power_state_ARM_PWR_LVL1 == ARM_LOCAL_STATE_RUN)
	{
		SCMI_SET_PWR_STATE_LVL(scmi_pwr_state, 0,
			scmi_power_state_off);
		SCMI_SET_PWR_STATE_MAX_PWR_LVL(scmi_pwr_state, 0);
	}

	if(psci_power_state_ARM_PWR_LVL0 != ARM_LOCAL_STATE_RUN &&
		psci_power_state_ARM_PWR_LVL1 != ARM_LOCAL_STATE_RUN &&
		psci_power_state_ARM_PWR_LVL2 == ARM_LOCAL_STATE_RUN)
	{
		SCMI_SET_PWR_STATE_LVL(scmi_pwr_state, 0,
			scmi_power_state_off);
		SCMI_SET_PWR_STATE_LVL(scmi_pwr_state, 1,
			scmi_power_state_off);
		SCMI_SET_PWR_STATE_MAX_PWR_LVL(scmi_pwr_state, 1);
	}
	
	return 0;
	
}

int set_pwr_state_off(uint32_t scmi_pwr_state, unsigned int core_pos)
{
	/*
		css_scp_core_pos_to_scmi_channel(plat_my_core_pos(),
			&domain_id, &channel_id);
		目前只有一个全局的scmi_handle
		ret = scmi_pwr_state_set(scmi_handles[channel_id],
			domain_id, scmi_pwr_state);
		if (ret != SCMI_E_QUEUED && ret != SCMI_E_SUCCESS) {
			ERROR("SCMI set power state command return 0x%x unexpected\n",
				ret);
		panic();
	}*/
	unsigned int channel_id;
	unsigned int domain_id;
	uint32_t pwr_state_set_msg_flag = SCMI_PWR_STATE_SET_FLAG_ASYNC;
	if(core_pos >=16)
	{
		return -1;
	}
	channel_id = get_scmi_channel_id(core_pos);
	domain_id = get_scmi_domain_id(core_pos);
	if(channel_id !=0 || domain_id != 0)
	{
		return -1;
	}
	// get channel 
	scmi_channel_t *ch = &scmi_channels[channel_id];
	if(!ch->is_initialized || ch->scmi_mbx_mem_id > 16)
	{
		return -1;
	}
	mailbox_mem_t *mbx_mem = &mailbox_mem_table[ch->scmi_mbx_mem_id];
	// 去除了对锁的操作
	if(SCMI_IS_CHANNEL_FREE(mbx_mem->status))
	{
		return -1;
	}

	mbx_mem->msg_header = SCMI_MSG_CREATE(SCMI_PWR_DMN_PROTO_ID,
			SCMI_PWR_STATE_SET_MSG, 0);
	mbx_mem->len = SCMI_PWR_STATE_SET_MSG_LEN;
	mbx_mem->flags = SCMI_FLAG_RESP_POLL;
	// 这里需要修改,还不清楚什么操作.
	// SCMI_PAYLOAD_ARG3(mbx_mem->payload, pwr_state_set_msg_flag,
	// 					domain_id, scmi_pwr_state);
	mbx_mem->payload[0] = pwr_state_set_msg_flag;
	mbx_mem->payload[1] = domain_id;
	mbx_mem->payload[2] = scmi_pwr_state;

	// scmi_send_sync_command(ch); 调用了SCMI_MARK_CHANNEL_BUSY(mbx_mem->status);
	// SCMI_MARK_CHANNEL_BUSY(mbx_mem->status);	// 该定义中已经对mbx_mem->status的状态进行了判断,因此,不需要
	//进行assert操作,故修改如下.
	(mbx_mem->status) &= ~(SCMI_CH_STATUS_FREE_MASK << SCMI_CH_STATUS_FREE_SHIFT);

	// 以下都是不需要验证的边界。因为只是return ret,没有影响到空间状态
	// SCMI_PAYLOAD_RET_VAL1(mbx_mem->payload, ret);	// 返回mbx_mem->payload[0]的值
	// assert(mbx_mem->len == SCMI_PWR_STATE_SET_RESP_LEN);
	// assert(token == SCMI_MSG_GET_TOKEN(mbx_mem->msg_header));

	// scmi_put_channel(ch);
	// return ret;
	return 0; 
}



int main(int arg, char **args)
{
	unsigned int channel_id;
	unsigned int domain_id;
	/*
		根据core position 获取channel id；core position从0-15，获得的值都为0
		domain也是一样。
	*/
	channel_id = get_scmi_channel_id(15);
	domain_id = get_scmi_domain_id(15);
	printf("%x %x", channel_id,domain_id);
	return 0;
}
