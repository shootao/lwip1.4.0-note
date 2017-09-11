/*
 * Copyright (c) 2001-2004 Swedish Institute of Computer Science.
 * All rights reserved. 
 * 
 * Redistribution and use in source and binary forms, with or without modification, 
 * are permitted provided that the following conditions are met:
 *
 * 1. Redistributions of source code must retain the above copyright notice,
 *    this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 *    this list of conditions and the following disclaimer in the documentation
 *    and/or other materials provided with the distribution.
 * 3. The name of the author may not be used to endorse or promote products
 *    derived from this software without specific prior written permission. 
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHOR ``AS IS'' AND ANY EXPRESS OR IMPLIED 
 * WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF 
 * MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT 
 * SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, 
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT 
 * OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS 
 * INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN 
 * CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING 
 * IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY 
 * OF SUCH DAMAGE.
 *
 * This file is part of the lwIP TCP/IP stack.
 * 
 * Author: Adam Dunkels <adam@sics.se>
 *
 */
#ifndef __LWIP_TCP_H__
#define __LWIP_TCP_H__

#include "lwip/opt.h"

#if LWIP_TCP /* don't build if not configured for use in lwipopts.h */

#include "lwip/sys.h"
#include "lwip/mem.h"
#include "lwip/pbuf.h"
#include "lwip/ip.h"
#include "lwip/icmp.h"
#include "lwip/err.h"

#ifdef __cplusplu
extern "C" {
#endif

struct tcp_pcb;

/** Function prototype for tcp accept callback functions. Called when a new
 * connection can be accepted on a listening pcb.
 *
 * @param arg Additional argument to pass to the callback function (@see tcp_arg())
 * @param newpcb The new connection pcb
 * @param err An error code if there has been an error accepting.
 *            Only return ERR_ABRT if you have called tcp_abort from within the
 *            callback function!
 */
typedef err_t (*tcp_accept_fn)(void *arg, struct tcp_pcb *newpcb, err_t err);

/** Function prototype for tcp receive callback functions. Called when data has
 * been received.
 *
 * @param arg Additional argument to pass to the callback function (@see tcp_arg())
 * @param tpcb The connection pcb which received data
 * @param p The received data (or NULL when the connection has been closed!)
 * @param err An error code if there has been an error receiving
 *            Only return ERR_ABRT if you have called tcp_abort from within the
 *            callback function!
 */
typedef err_t (*tcp_recv_fn)(void *arg, struct tcp_pcb *tpcb,
                             struct pbuf *p, err_t err);

/** Function prototype for tcp sent callback functions. Called when sent data has
 * been acknowledged by the remote side. Use it to free corresponding resources.
 * This also means that the pcb has now space available to send new data.
 *
 * @param arg Additional argument to pass to the callback function (@see tcp_arg())
 * @param tpcb The connection pcb for which data has been acknowledged
 * @param len The amount of bytes acknowledged
 * @return ERR_OK: try to send some data by calling tcp_output
 *            Only return ERR_ABRT if you have called tcp_abort from within the
 *            callback function!
 */
typedef err_t (*tcp_sent_fn)(void *arg, struct tcp_pcb *tpcb,
                              u16_t len);

/** Function prototype for tcp poll callback functions. Called periodically as
 * specified by @see tcp_poll.
 *
 * @param arg Additional argument to pass to the callback function (@see tcp_arg())
 * @param tpcb tcp pcb
 * @return ERR_OK: try to send some data by calling tcp_output
 *            Only return ERR_ABRT if you have called tcp_abort from within the
 *            callback function!
 */
typedef err_t (*tcp_poll_fn)(void *arg, struct tcp_pcb *tpcb);

/** Function prototype for tcp error callback functions. Called when the pcb
 * receives a RST or is unexpectedly closed for any other reason.
 *
 * @note The corresponding pcb is already freed when this callback is called!
 *
 * @param arg Additional argument to pass to the callback function (@see tcp_arg())
 * @param err Error code to indicate why the pcb has been closed
 *            ERR_ABRT: aborted through tcp_abort or by a TCP timer
 *            ERR_RST: the connection was reset by the remote host
 */
typedef void  (*tcp_err_fn)(void *arg, err_t err);

/** Function prototype for tcp connected callback functions. Called when a pcb
 * is connected to the remote side after initiating a connection attempt by
 * calling tcp_connect().
 *
 * @param arg Additional argument to pass to the callback function (@see tcp_arg())
 * @param tpcb The connection pcb which is connected
 * @param err An unused error code, always ERR_OK currently ;-) TODO!
 *            Only return ERR_ABRT if you have called tcp_abort from within the
 *            callback function!
 *
 * @note When a connection attempt fails, the error callback is currently called!
 */
typedef err_t (*tcp_connected_fn)(void *arg, struct tcp_pcb *tpcb, err_t err);

enum tcp_state {
  CLOSED      = 0,
  LISTEN      = 1,
  SYN_SENT    = 2,
  SYN_RCVD    = 3,
  ESTABLISHED = 4,
  FIN_WAIT_1  = 5,
  FIN_WAIT_2  = 6,
  CLOSE_WAIT  = 7,
  CLOSING     = 8,
  LAST_ACK    = 9,
  TIME_WAIT   = 10/*关闭成功，等待网络中*/
};

#if LWIP_CALLBACK_API
  /* Function to call when a listener has been connected.
   * @param arg user-supplied argument (tcp_pcb.callback_arg)
   * @param pcb a new tcp_pcb that now is connected
   * @param err an error argument (TODO: that is current always ERR_OK?)
   * @return ERR_OK: accept the new connection,
   *                 any other err_t abortsthe new connection
   */
#define DEF_ACCEPT_CALLBACK  tcp_accept_fn accept;
#else /* LWIP_CALLBACK_API */
#define DEF_ACCEPT_CALLBACK
#endif /* LWIP_CALLBACK_API */

/**
 * members common to struct tcp_pcb and struct tcp_listen_pcb
 */
/*x先定义一个宏，事实上在LWIP中定义了两种类型的TCP控制块，一种专门用于描述处于LISTEN状态的
链接，另一种用于描述其他状态的链接，这个宏工定义了两种类型控制块共有的一些字段*/
#define TCP_PCB_COMMON(type) \ /*type为宏参数*/
  type *next; /* for the linked list *//*将控制块组成链表*/ \
  enum tcp_state state; /* TCP state *//*链接状态*/ \
  u8_t prio; \  //优先级，可用于回收低优先级控制块
  void *callback_arg; \    //用户自定义数据
  /* the accept callback for listen- and normal pcbs, if LWIP_CALLBACK_API */ \
  DEF_ACCEPT_CALLBACK \
  /* ports are in host byte order */ \
  u16_t local_port


/* the TCP protocol control block */
struct tcp_pcb {
/** common PCB members */
  IP_PCB;
/** protocol specific PCB members */
  TCP_PCB_COMMON(struct tcp_pcb);

  /* ports are in host byte order */
  u16_t remote_port;
  
  u8_t flags;
#define TF_ACK_DELAY   ((u8_t)0x01U)   /* Delayed ACK. */
#define TF_ACK_NOW     ((u8_t)0x02U)   /* Immediate ACK. *//*定义掩码*/
#define TF_INFR        ((u8_t)0x04U)   /* In fast recovery. *///链接处于快速处于重传状态
#define TF_TIMESTAMP   ((u8_t)0x08U)   /* Timestamp option enabled *//*连接的时间撮选项已使能*/
#define TF_RXCLOSED    ((u8_t)0x10U)   /* rx closed by tcp_shutdown */
#define TF_FIN         ((u8_t)0x20U)   /* Connection was closed locally (FIN segment enqueued). *///应用层关闭该链接
#define TF_NODELAY     ((u8_t)0x40U)   /* Disable Nagle algorithm */
#define TF_NAGLEMEMERR ((u8_t)0x80U)   /* nagle enabled, memerr, try to output to prevent delayed ACK to happen *///本地缓冲溢出

  /* the rest of the fields are in host byte order
     as we have to do some math with them */
  /* receiver variables */
  
  //http://blog.csdn.net/jiangjunjie_2005/article/details/26051399
/*
                                rcv_ann_wnd = 9   
              |——————————————————rcv_wnd = 9————————--| 
              |                                       |
---------------------------------------------------------------------------------------------
. . . | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 | 17 |  |  |  |  |  |
----------------------------------------------------------------------------------------------
                |                                       |
             rcv_nxt=5                             rcv_ann_right_edge=14
*/// 接收窗口相关字段
  u32_t rcv_nxt;   /* next seqno expected *///下一个期望接受的字节序号，即它向发送端的ACK的序号
  u16_t rcv_wnd;   /* receiver window available *///当前接收窗口的大小，会随着数据的接收与递交动态变化
  u16_t rcv_ann_wnd; /* receiver window to announce *///将向对方通告的窗口大小，会随着数据的接收与递交动态变化,这个值在报文发送时会被填在首部的窗口大小字段
  u32_t rcv_ann_right_edge; /* announced right edge of window *///上一次窗口通告时窗口的右边界值

  /* Timers 下面这个字段记录了控制块上一次活动的系统时间，也可以表示链接处于某个状态的时间，控制块其他各计数器都基于tmr值来实现*/
  u32_t tmr;
  /*下面两个字段由于周期性的调一个函数，polltmr会周期性增加，当polliterval时，poll函数会被回调*/
  u8_t polltmr, pollinterval;
  
  /* Retransmission timer. 重传定时器,该值随是随时间递增(500ms加1)，当大于rto的值时重传报文*/
  s16_t rtime;
  
  u16_t mss;   /* maximum segment size 对方可接受的最大报文大小*/
  
  /* RTT (round trip time) estimation variables */
  /*RTT估计相关的参数*/
  u32_t rttest; /* RTT estimate in 500ms ticks *RTT估计时，以500ms为周期递增（某个报文段计时）*/
  u32_t rtseq;  /* sequence number being timed 用于测试RTT的报文字段序号*/
  s16_t sa, sv; /* @todo document this RTT估计的平均值及其时间差*/

  s16_t rto;    /* re-transmission time-out 重发超时时间（超时间隔），根据上面的几个值计算出来*/
  u8_t nrtx;    /* number of retransmissions 重发次数，多次重发时，会使用该字段设置rto的值*/

  /* fast retransmit/recovery 快速重传与恢复相关字段*/
  u32_t lastack; /* Highest acknowledged seqno.接收到的最大确认号 */
  u8_t dupacks; /*上述最大确认号被重复收到的次数*/
  //(pcb->snd_wnd, pcb->cwnd);
  /* congestion avoidance/control variables 阻塞相关的字段*/
  u16_t cwnd;  /*连接当前的阻塞窗口大小*/
  u16_t ssthresh;/*拥塞避免算法启动阈值*/

  /* sender variables发送窗口相关字段 */
  /*

                                
              |——————————————————sndv_wnd = 9————————-| 
              |                        |              |
---------------------------------------------------------------------------------------------
. . . | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 | 17 |  |  |  |  |  |
----------------------------------------------------------------------------------------------
            |                          |                      |
          lasttack=5                 snd_next=11             snd_lbb=15

  */
  u32_t snd_nxt;   /* next new seqno to be sent 下一个将要发送的数据序号*/
  u16_t snd_wnd;   /* sender window 发送窗口的大小*/
  u32_t snd_wl1, snd_wl2; /* Sequence and acknowledgement numbers of last 上一次窗口更新时收到的数据序号和确认序号
                             window update. */
  u32_t snd_lbb;       /* Sequence number of next byte to be buffered. 下一个被缓冲的应用程序数据的编号*/

  u16_t acked;/*上一次成功发送的字节数*/
  
  u16_t snd_buf;   /* Available buffer space for sending (in bytes).可以使用的缓冲区大小 */
#define TCP_SNDQUEUELEN_OVERFLOW (0xffffU-3)
  u16_t snd_queuelen;  //Available buffer space for sending (in tcp_segs).缓冲区占用pbuf的个数 

#if TCP_OVERSIZE
  /* Extra bytes available at the end of the last pbuf in unsent. */
  u16_t unsent_oversize;/**/
#endif /* TCP_OVERSIZE */ 

  /* These are ordered by sequence number: 下面三个字段是用户数据缓冲的队列指针*/
  struct tcp_seg *unsent;   /* Unsent (queued) segments.未发送的报文段队列 */
  struct tcp_seg *unacked;  /* Sent but unacknowledged segments. 发送了但未收到的无序报文段队列*/
#if TCP_QUEUE_OOSEQ  
  struct tcp_seg *ooseq;    /* Received out of sequence segments. 接收到的无序de报文段队列*/
#endif /* TCP_QUEUE_OOSEQ */  /* Function to be called when more send buffer space is available. 数据被成功发送后被调用*/
  tcp_sent_fn sent;
  /* Function to be called when (in-sequence) data has arrived. 数据被成功接收后被调用*/
  tcp_recv_fn recv;
  /* Function to be called when a connection has been set up. 连接建立后被调用*/
  tcp_connected_fn connected;
  /* Function which is called periodically. 该函数被内核周期性调用*/
  tcp_poll_fn poll;
  /* Function to be called whenever a fatal error occurs. 连接发生错误时被调用*/
  tcp_err_fn errf;
#endif /* LWIP_CALLBACK_API */

#if LWIP_TCP_TIMESTAMPS
  u32_t ts_lastacksent;
  u32_t ts_recent;
#endif /* LWIP_TCP_TIMESTAMPS */

  /* idle time before KEEPALIVE is sent */
  u32_t keep_idle;  /*保活计时器的上限值*/
#if LWIP_TCP_KEEPALIVE
  u32_t keep_intvl;/**/
  u32_t keep_cnt;
#endif /* LWIP_TCP_KEEPALIVE */
  
  /* Persist timer counter */
  u32_t persist_cnt;/*坚持定时器计数值*/
  /* Persist timer back-off */
  u8_t persist_backoff;/*坚持定时器探查报文发送的数目*/

  /* KEEPALIVE counter */
  u8_t keep_cnt_sent;/*保活报文发送的次数*/
};

/*下面定义用于LISTEN状态TCP连接的控制块结构*/
struct tcp_pcb_listen {  
/* Common members of all PCB types */
  IP_PCB;
/* Protocol specific PCB members */
  TCP_PCB_COMMON(struct tcp_pcb_listen);

#if TCP_LISTEN_BACKLOG
  u8_t backlog;
  u8_t accepts_pending;
#endif /* TCP_LISTEN_BACKLOG */
};

#if LWIP_EVENT_API

enum lwip_event {
  LWIP_EVENT_ACCEPT,
  LWIP_EVENT_SENT,
  LWIP_EVENT_RECV,
  LWIP_EVENT_CONNECTED,
  LWIP_EVENT_POLL,
  LWIP_EVENT_ERR
};

err_t lwip_tcp_event(void *arg, struct tcp_pcb *pcb,
         enum lwip_event,
         struct pbuf *p,
         u16_t size,
         err_t err);

#endif /* LWIP_EVENT_API */

/* Application program's interface: */
struct tcp_pcb * tcp_new     (void);

void             tcp_arg     (struct tcp_pcb *pcb, void *arg);
void             tcp_accept  (struct tcp_pcb *pcb, tcp_accept_fn accept);
void             tcp_recv    (struct tcp_pcb *pcb, tcp_recv_fn recv);
void             tcp_sent    (struct tcp_pcb *pcb, tcp_sent_fn sent);
void             tcp_poll    (struct tcp_pcb *pcb, tcp_poll_fn poll, u8_t interval);
void             tcp_err     (struct tcp_pcb *pcb, tcp_err_fn err);

#define          tcp_mss(pcb)             (((pcb)->flags & TF_TIMESTAMP) ? ((pcb)->mss - 12)  : (pcb)->mss)
#define          tcp_sndbuf(pcb)          ((pcb)->snd_buf)
#define          tcp_sndqueuelen(pcb)     ((pcb)->snd_queuelen)
#define          tcp_nagle_disable(pcb)   ((pcb)->flags |= TF_NODELAY)
#define          tcp_nagle_enable(pcb)    ((pcb)->flags &= ~TF_NODELAY)
#define          tcp_nagle_disabled(pcb)  (((pcb)->flags & TF_NODELAY) != 0)

#if TCP_LISTEN_BACKLOG
#define          tcp_accepted(pcb) do { \
  LWIP_ASSERT("pcb->state == LISTEN (called for wrong pcb?)", pcb->state == LISTEN); \
  (((struct tcp_pcb_listen *)(pcb))->accepts_pending--); } while(0)
#else  /* TCP_LISTEN_BACKLOG */
#define          tcp_accepted(pcb) LWIP_ASSERT("pcb->state == LISTEN (called for wrong pcb?)", \
                                               pcb->state == LISTEN)
#endif /* TCP_LISTEN_BACKLOG */

void             tcp_recved  (struct tcp_pcb *pcb, u16_t len);
err_t            tcp_bind    (struct tcp_pcb *pcb, ip_addr_t *ipaddr,
                              u16_t port);
err_t            tcp_connect (struct tcp_pcb *pcb, ip_addr_t *ipaddr,
                              u16_t port, tcp_connected_fn connected);

struct tcp_pcb * tcp_listen_with_backlog(struct tcp_pcb *pcb, u8_t backlog);
#define          tcp_listen(pcb) tcp_listen_with_backlog(pcb, TCP_DEFAULT_LISTEN_BACKLOG)

void             tcp_abort (struct tcp_pcb *pcb);
err_t            tcp_close   (struct tcp_pcb *pcb);
err_t            tcp_shutdown(struct tcp_pcb *pcb, int shut_rx, int shut_tx);

/* Flags for "apiflags" parameter in tcp_write */
#define TCP_WRITE_FLAG_COPY 0x01
#define TCP_WRITE_FLAG_MORE 0x02

err_t            tcp_write   (struct tcp_pcb *pcb, const void *dataptr, u16_t len,
                              u8_t apiflags);

void             tcp_setprio (struct tcp_pcb *pcb, u8_t prio);

#define TCP_PRIO_MIN    1
#define TCP_PRIO_NORMAL 64
#define TCP_PRIO_MAX    127

err_t            tcp_output  (struct tcp_pcb *pcb);


const char* tcp_debug_state_str(enum tcp_state s);


#ifdef __cplusplus
}
#endif

#endif /* LWIP_TCP */

#endif /* __LWIP_TCP_H__ */
