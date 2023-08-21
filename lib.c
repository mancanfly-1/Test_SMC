#include "TIPC.h"
typedef unsigned long long int uint64_t;

uint64_t find_free_port_id(void)
{
    static uint64_t i = 1;
    int n = 0;

    while (n < 2) {
        ++i;
        if (i == NPORT) {
            i = 2;
            ++n;
        }
        if (port_table[i].used == PORT_UNUSED)
            return i;
    }
    panic("no free pid");
}


path_id_t find_free_path_id(void)
{
    static uint64_t i = 1;
    int n = 0;

    while (n < 2) {
        ++i;
        if (i == NPORT) {
            i = 2;
            ++n;
        }
        if (path_table[i].state == PATH_UNUSED)
            return i;
    }
    panic("no free pid");
}

uint32_t get_first_waiting_port_chan(uint32_t port_id)
{
    for (int i = 0; i < NPORT; i++)
    {
        if(chan_table[i].port_id == port_id)
        {
            return i;
        }
    }    
    panic("no waiting for fort");
}

// 用于获得一个free的queue id
uint64_t get_free_queue(void)
{
    static uint64_t i;
    while(i < NMSG_QUEUE)
    {
        uint64_t j = i++;
        if (is_queue_type(j, MSG_QUEUE_TYPE_FREE))
            return j;

    }
    panic("woo, no free queue to alloc!");
    return NMSG_QUEUE;
}