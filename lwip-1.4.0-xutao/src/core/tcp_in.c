/**
 * @file
 * Transmission Control Protocol, incoming traffic
 *
 * The input processing functions of the TCP layer.
 *
 * These functions are generally called in the order (ip_input() ->)
 * tcp_input() -> * tcp_process() -> tcp_receive() (-> application).
 * 
 */

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

#include "lwip/opt.h"

#if LWIP_TCP /* don't build if not configured for use in lwipopts.h */

#include "lwip/tcp_impl.h"
#include "lwip/def.h"
#include "lwip/ip_addr.h"
#include "lwip/netif.h"
#include "lwip/mem.h"
#include "lwip/memp.h"
#include "lwip/inet_chksum.h"
#include "lwip/stats.h"
#include "lwip/snmp.h"
#include "arch/perf.h"

/* These variables are global to all functions involved in the input
   processing of TCP segments. They are set by the tcp_input()
   function. */
static struct tcp_seg inseg;
static struct tcp_hdr *tcphdr;
static struct ip_hdr *iphdr;
static u32_t seqno, ackno;
static u8_t flags;
static u16_t tcplen;

static u8_t recv_flags;
static struct pbuf *recv_data;

struct tcp_pcb *tcp_input_pcb;

/* Forward declarations. */
static err_t tcp_process(struct tcp_pcb *pcb);
static void tcp_receive(struct tcp_pcb *pcb);
static void tcp_parseopt(struct tcp_pcb *pcb);

static err_t tcp_listen_input(struct tcp_pcb_listen *pcb);
static err_t tcp_timewait_input(struct tcp_pcb *pcb);

/**
 * The initial input processing of TCP. It verifies the TCP header, demultiplexes
 * the segment between the PCBs and passes it on to tcp_process(), which implements
 * the TCP finite state machine. This function is called by the IP layer (in
 * ip_input()).
 *
 * @param p received TCP segment to process (p->payload pointing to the IP header)
 * @param inp network interface on which this segment was received
 */
void
tcp_input(struct pbuf *p, struct netif *inp)
{
  struct tcp_pcb *pcb, *prev;
  struct tcp_pcb_listen *lpcb;
#if SO_REUSE
  struct tcp_pcb *lpcb_prev = NULL;
  struct tcp_pcb_listen *lpcb_any = NULL;
#endif /* SO_REUSE */
  u8_t hdrlen;
  err_t err;

  PERF_START;

  TCP_STATS_INC(tcp.recv);
  snmp_inc_tcpinsegs();

  iphdr = (struct ip_hdr *)p->payload;
  tcphdr = (struct tcp_hdr *)((u8_t *)p->payload + IPH_HL(iphdr) * 4);

#if TCP_INPUT_DEBUG
  tcp_debug_print(tcphdr);
#endif

  /* remove header from payload */
  if (pbuf_header(p, -((s16_t)(IPH_HL(iphdr) * 4))) || (p->tot_len < sizeof(struct tcp_hdr))) {
    /* drop short packets */
    LWIP_DEBUGF(TCP_INPUT_DEBUG, ("tcp_input: short packet (%"U16_F" bytes) discarded\n", p->tot_len));
    TCP_STATS_INC(tcp.lenerr);
    TCP_STATS_INC(tcp.drop);
    snmp_inc_tcpinerrs();
    pbuf_free(p);
    return;
  }

  /* Don't even process incoming broadcasts/multicasts. */
  if (ip_addr_isbroadcast(&current_iphdr_dest, inp) ||
      ip_addr_ismulticast(&current_iphdr_dest)) {
    TCP_STATS_INC(tcp.proterr);
    TCP_STATS_INC(tcp.drop);
    snmp_inc_tcpinerrs();
    pbuf_free(p);
    return;
  }

#if CHECKSUM_CHECK_TCP
  /* Verify TCP checksum. */
  if (inet_chksum_pseudo(p, ip_current_src_addr(), ip_current_dest_addr(),
      IP_PROTO_TCP, p->tot_len) != 0) {
      LWIP_DEBUGF(TCP_INPUT_DEBUG, ("tcp_input: packet discarded due to failing checksum 0x%04"X16_F"\n",
        inet_chksum_pseudo(p, ip_current_src_addr(), ip_current_dest_addr(),
      IP_PROTO_TCP, p->tot_len)));
#if TCP_DEBUG
    tcp_debug_print(tcphdr);
#endif /* TCP_DEBUG */
    TCP_STATS_INC(tcp.chkerr);
    TCP_STATS_INC(tcp.drop);
    snmp_inc_tcpinerrs();
    pbuf_free(p);
    return;
  }
#endif

  /* Move the payload pointer in the pbuf so that it points to the
     TCP data instead of the TCP header. */
  hdrlen = TCPH_HDRLEN(tcphdr);
  if(pbuf_header(p, -(hdrlen * 4))){
    /* drop short packets */
    LWIP_DEBUGF(TCP_INPUT_DEBUG, ("tcp_input: short packet\n"));
    TCP_STATS_INC(tcp.lenerr);
    TCP_STATS_INC(tcp.drop);
    snmp_inc_tcpinerrs();
    pbuf_free(p);
    return;
  }

  /* Convert fields in TCP header to host byte order. */
  tcphdr->src = ntohs(tcphdr->src);
  tcphdr->dest = ntohs(tcphdr->dest);
  seqno = tcphdr->seqno = ntohl(tcphdr->seqno);
  ackno = tcphdr->ackno = ntohl(tcphdr->ackno);
  tcphdr->wnd = ntohs(tcphdr->wnd);

  flags = TCPH_FLAGS(tcphdr);
  tcplen = p->tot_len + ((flags & (TCP_FIN | TCP_SYN)) ? 1 : 0);

  /* Demultiplex an incoming segment. First, we check if it is destined
     for an active connection. */
  prev = NULL;

  /*遍历tcp_active_pcbs，*/
  for(pcb = tcp_active_pcbs; pcb != NULL; pcb = pcb->next) {
    LWIP_ASSERT("tcp_input: active pcb->state != CLOSED", pcb->state != CLOSED);
    LWIP_ASSERT("tcp_input: active pcb->state != TIME-WAIT", pcb->state != TIME_WAIT);
    LWIP_ASSERT("tcp_input: active pcb->state != LISTEN", pcb->state != LISTEN);
    if (pcb->remote_port == tcphdr->src &&
       pcb->local_port == tcphdr->dest &&
       ip_addr_cmp(&(pcb->remote_ip), &current_iphdr_src) &&
       ip_addr_cmp(&(pcb->local_ip), &current_iphdr_dest)) {

      /* Move this PCB to the front of the list so that subsequent
         lookups will be faster (we exploit locality in TCP segment
         arrivals). */
      LWIP_ASSERT("tcp_input: pcb->next != pcb (before cache)", pcb->next != pcb);
      if (prev != NULL) {
        prev->next = pcb->next;
        pcb->next = tcp_active_pcbs;
        tcp_active_pcbs = pcb;
      }
      LWIP_ASSERT("tcp_input: pcb->next != pcb (after cache)", pcb->next != pcb);
      break;
    }
    prev = pcb;
  }

  if (pcb == NULL) {
    /* If it did not go to an active connection, we check the connections
       in the TIME-WAIT state. */
    for(pcb = tcp_tw_pcbs; pcb != NULL; pcb = pcb->next) {
      LWIP_ASSERT("tcp_input: TIME-WAIT pcb->state == TIME-WAIT", pcb->state == TIME_WAIT);
      if (pcb->remote_port == tcphdr->src &&
         pcb->local_port == tcphdr->dest &&
         ip_addr_cmp(&(pcb->remote_ip), &current_iphdr_src) &&
         ip_addr_cmp(&(pcb->local_ip), &current_iphdr_dest)) {
        /* We don't really care enough to move this PCB to the front
           of the list since we are not very likely to receive that
           many segments for connections in TIME-WAIT. */
        LWIP_DEBUGF(TCP_INPUT_DEBUG, ("tcp_input: packed for TIME_WAITing connection.\n"));
        tcp_timewait_input(pcb);/*控制块处于TIME_WAIT状态的控制块处理输入报文的函数*/
        pbuf_free(p);
        return;
      }
    }

    /* Finally, if we still did not get a match, we check all PCBs that
       are LISTENing for incoming connections. */
    prev = NULL;
    for(lpcb = tcp_listen_pcbs.listen_pcbs; lpcb != NULL; lpcb = lpcb->next) {
      if (lpcb->local_port == tcphdr->dest) {
#if SO_REUSE
        if (ip_addr_cmp(&(lpcb->local_ip), &current_iphdr_dest)) {
          /* found an exact match */
          break;
        } else if(ip_addr_isany(&(lpcb->local_ip))) {
          /* found an ANY-match */
          lpcb_any = lpcb;
          lpcb_prev = prev;
        }
#else /* SO_REUSE */
        if (ip_addr_cmp(&(lpcb->local_ip), &current_iphdr_dest) ||
            ip_addr_isany(&(lpcb->local_ip))) {
          /* found a match */
          break;
        }
#endif /* SO_REUSE */
      }
      prev = (struct tcp_pcb *)lpcb;
    }
#if SO_REUSE
    /* first try specific local IP */
    if (lpcb == NULL) {
      /* only pass to ANY if no specific local IP has been found */
      lpcb = lpcb_any;
      prev = lpcb_prev;
    }
#endif /* SO_REUSE */
    if (lpcb != NULL) {
      /* Move this PCB to the front of the list so that subsequent
         lookups will be faster (we exploit locality in TCP segment
         arrivals). */
      if (prev != NULL) {
        ((struct tcp_pcb_listen *)prev)->next = lpcb->next;
              /* our successor is the remainder of the listening list */
        lpcb->next = tcp_listen_pcbs.listen_pcbs;
              /* put this listening pcb at the head of the listening list */
        tcp_listen_pcbs.listen_pcbs = lpcb;
      }
    
      LWIP_DEBUGF(TCP_INPUT_DEBUG, ("tcp_input: packed for LISTENing connection.\n"));
      tcp_listen_input(lpcb);
      pbuf_free(p);
      return;
    }
  }

#if TCP_INPUT_DEBUG
  LWIP_DEBUGF(TCP_INPUT_DEBUG, ("+-+-+-+-+-+-+-+-+-+-+-+-+-+- tcp_input: flags "));
  tcp_debug_print_flags(TCPH_FLAGS(tcphdr));
  LWIP_DEBUGF(TCP_INPUT_DEBUG, ("-+-+-+-+-+-+-+-+-+-+-+-+-+-+\n"));
#endif /* TCP_INPUT_DEBUG */


  if (pcb != NULL) {
    /* The incoming segment belongs to a connection. */
#if TCP_INPUT_DEBUG
#if TCP_DEBUG
    tcp_debug_print_state(pcb->state);
#endif /* TCP_DEBUG */
#endif /* TCP_INPUT_DEBUG */

    /* Set up a tcp_seg structure. */
    inseg.next = NULL;
    inseg.len = p->tot_len;
    inseg.p = p;
    inseg.tcphdr = tcphdr;

    recv_data = NULL;
    recv_flags = 0;

    /* If there is data which was previously "refused" by upper layer */
    if (pcb->refused_data != NULL) {
      /* Notify again application with data previously received. */
      LWIP_DEBUGF(TCP_INPUT_DEBUG, ("tcp_input: notify kept packet\n"));
      TCP_EVENT_RECV(pcb, pcb->refused_data, ERR_OK, err);
      if (err == ERR_OK) {
        pcb->refused_data = NULL;
      } else if ((err == ERR_ABRT) || (tcplen > 0)) {
        /* if err == ERR_ABRT, 'pcb' is already deallocated */
        /* Drop incoming packets because pcb is "full" (only if the incoming
           segment contains data). */
        LWIP_DEBUGF(TCP_INPUT_DEBUG, ("tcp_input: drop incoming packets, because pcb is \"full\"\n"));
        TCP_STATS_INC(tcp.drop);
        snmp_inc_tcpinerrs();
        pbuf_free(p);
        return;
      }
    }
    tcp_input_pcb = pcb;
    err = tcp_process(pcb);
    /* A return value of ERR_ABRT means that tcp_abort() was called
       and that the pcb has been freed. If so, we don't do anything. */
    if (err != ERR_ABRT) {
      if (recv_flags & TF_RESET) {
        /* TF_RESET means that the connection was reset by the other
           end. We then call the error callback to inform the
           application that the connection is dead before we
           deallocate the PCB. */
        TCP_EVENT_ERR(pcb->errf, pcb->callback_arg, ERR_RST);
        tcp_pcb_remove(&tcp_active_pcbs, pcb);
        memp_free(MEMP_TCP_PCB, pcb);
      } else if (recv_flags & TF_CLOSED) {
        /* The connection has been closed and we will deallocate the
           PCB. */
        tcp_pcb_remove(&tcp_active_pcbs, pcb);
        memp_free(MEMP_TCP_PCB, pcb);
      } else {
        err = ERR_OK;
        /* If the application has registered a "sent" function to be
           called when new send buffer space is available, we call it
           now. */
        if (pcb->acked > 0) {
          TCP_EVENT_SENT(pcb, pcb->acked, err);
          if (err == ERR_ABRT) {
            goto aborted;
          }
        }

        if (recv_data != NULL) {
          LWIP_ASSERT("pcb->refused_data == NULL", pcb->refused_data == NULL);
          if (pcb->flags & TF_RXCLOSED) {
            /* received data although already closed -> abort (send RST) to
               notify the remote host that not all data has been processed */
            pbuf_free(recv_data);
            tcp_abort(pcb);
            goto aborted;
          }
          if (flags & TCP_PSH) {
            recv_data->flags |= PBUF_FLAG_PUSH;
          }

          /* Notify application that data has been received. */
          TCP_EVENT_RECV(pcb, recv_data, ERR_OK, err);
          if (err == ERR_ABRT) {
            goto aborted;
          }

          /* If the upper layer can't receive this data, store it */
          if (err != ERR_OK) {
            pcb->refused_data = recv_data;
            LWIP_DEBUGF(TCP_INPUT_DEBUG, ("tcp_input: keep incoming packet, because pcb is \"full\"\n"));
          }
        }

        /* If a FIN segment was received, we call the callback
           function with a NULL buffer to indicate EOF. */
        if (recv_flags & TF_GOT_FIN) {
          /* correct rcv_wnd as the application won't call tcp_recved()
             for the FIN's seqno */
          if (pcb->rcv_wnd != TCP_WND) {
            pcb->rcv_wnd++;
          }
          TCP_EVENT_CLOSED(pcb, err);
          if (err == ERR_ABRT) {
            goto aborted;
          }
        }

        tcp_input_pcb = NULL;
        /* Try to send something out. */
        tcp_output(pcb);
#if TCP_INPUT_DEBUG
#if TCP_DEBUG
        tcp_debug_print_state(pcb->state);
#endif /* TCP_DEBUG */
#endif /* TCP_INPUT_DEBUG */
      }
    }
    /* Jump target if pcb has been aborted in a callback (by calling tcp_abort()).
       Below this line, 'pcb' may not be dereferenced! */
aborted:
    tcp_input_pcb = NULL;
    recv_data = NULL;

    /* give up our reference to inseg.p */
    if (inseg.p != NULL)
    {
      pbuf_free(inseg.p);
      inseg.p = NULL;
    }
  } else {

    /* If no matching PCB was found, send a TCP RST (reset) to the
       sender. */
    LWIP_DEBUGF(TCP_RST_DEBUG, ("tcp_input: no PCB match found, resetting.\n"));
    if (!(TCPH_FLAGS(tcphdr) & TCP_RST)) {
      TCP_STATS_INC(tcp.proterr);
      TCP_STATS_INC(tcp.drop);
      tcp_rst(ackno, seqno + tcplen,
        ip_current_dest_addr(), ip_current_src_addr(),
        tcphdr->dest, tcphdr->src);
    }
    pbuf_free(p);
  }

  LWIP_ASSERT("tcp_input: tcp_pcbs_sane()", tcp_pcbs_sane());
  PERF_STOP("tcp_input");
}

/**
 * Called by tcp_input() when a segment arrives for a listening
 * connection (from tcp_input()).
 *
 * @param pcb the tcp_pcb_listen for which a segment arrived
 * @return ERR_OK if the segment was processed
 *         another err_t on error
 *
 * @note the return value is not (yet?) used in tcp_input()
 * @note the segment which arrived is saved in global variables, therefore only the pcb
 *       involved is passed as a parameter to this function
 */
/*处于LISTEN状态的控制块只能响应SYN握手包
函数通过SYN位来确认该报文是否为SYN报文，若是，则需要新建一个tcp_pcb结构，因为处于tcp_listen_pcbs上的控制块是tcp_pcb_listen结构的，
而其他链表上的控制块结构是tcp_pcb结构的，所以这里要新建一个tcp_pcb结构，并将tcp_pcb_listen结构中的相应字段拷贝到其中，同时在
tcp_active_pcbs链表中添加这个新的tcp_pcb结构，这样新的TCP控制块就处于tcp_active_pcbs中了。但是tcp_listen_pcbs结构一直在，以等待其他客户端的链接*/
static err_t
tcp_listen_input(struct tcp_pcb_listen *pcb)
{
  struct tcp_pcb *npcb;
  err_t rc;

  /* In the LISTEN state, we check for incoming SYN segments,
     creates a new PCB, and responds with a SYN|ACK. */
  if (flags & TCP_ACK) {
    /* For incoming segments with the ACK flag set, respond with a
       RST.因为SYN握手包不包含ACK */
    LWIP_DEBUGF(TCP_RST_DEBUG, ("tcp_listen_input: ACK in LISTEN, sending reset\n"));
    tcp_rst(ackno + 1, seqno + tcplen,
      ip_current_dest_addr(), ip_current_src_addr(),
      tcphdr->dest, tcphdr->src);
  } else if (flags & TCP_SYN) {
    LWIP_DEBUGF(TCP_DEBUG, ("TCP connection request %"U16_F" -> %"U16_F".\n", tcphdr->src, tcphdr->dest));
#if TCP_LISTEN_BACKLOG
    if (pcb->accepts_pending >= pcb->backlog) {
      LWIP_DEBUGF(TCP_DEBUG, ("tcp_listen_input: listen backlog exceeded for port %"U16_F"\n", tcphdr->dest));
      return ERR_ABRT;
    }
#endif /* TCP_LISTEN_BACKLOG */
    npcb = tcp_alloc(pcb->prio);    /*为新链接创建一个控制块*/
    /* If a new PCB could not be created (probably due to lack of memory),
       we don't do anything, but rely on the sender will retransmit the
       SYN at a time when we have more memory available. */
    if (npcb == NULL) {
      LWIP_DEBUGF(TCP_DEBUG, ("tcp_listen_input: could not allocate PCB\n"));
      TCP_STATS_INC(tcp.memerr);
      return ERR_MEM;
    }
#if TCP_LISTEN_BACKLOG
    pcb->accepts_pending++;
#endif /* TCP_LISTEN_BACKLOG */
    /* Set up the new PCB. */
    ip_addr_copy(npcb->local_ip, current_iphdr_dest);
    npcb->local_port = pcb->local_port;
    ip_addr_copy(npcb->remote_ip, current_iphdr_src);
    npcb->remote_port = tcphdr->src;
    npcb->state = SYN_RCVD;
    npcb->rcv_nxt = seqno + 1;
    npcb->rcv_ann_right_edge = npcb->rcv_nxt;
    npcb->snd_wnd = tcphdr->wnd;
    npcb->ssthresh = npcb->snd_wnd;
    npcb->snd_wl1 = seqno - 1;/* initialise to seqno-1 to force window update */
    npcb->callback_arg = pcb->callback_arg;
#if LWIP_CALLBACK_API
    npcb->accept = pcb->accept;
#endif /* LWIP_CALLBACK_API */
    /* inherit socket options */
    npcb->so_options = pcb->so_options & SOF_INHERITED;
    /* Register the new PCB so that we can begin receiving segments
       for it. *//*将新控制块加入tcp_active_pcbs链表*/
    TCP_REG(&tcp_active_pcbs, npcb);

    /* Parse any options in the SYN. */
    /*处理SYN包中的选项字段，并设置控制块flags字段中与响应选项对应的位，目前只支持最大报文段选项和时间撮选项*/
    tcp_parseopt(npcb);
#if TCP_CALCULATE_EFF_SEND_MSS
    npcb->mss = tcp_eff_send_mss(npcb->mss, &(npcb->remote_ip));/*设置最大报文长度*/
#endif /* TCP_CALCULATE_EFF_SEND_MSS */

    snmp_inc_tcppassiveopens();

    /* Send a SYN|ACK together with the MSS option. */
    /*构造SYN+ACK握手报文，且包含MSS选项，通告自己的最大报文大小*/
    rc = tcp_enqueue_flags(npcb, TCP_SYN | TCP_ACK);
    if (rc != ERR_OK) {
      tcp_abandon(npcb, 0);
      return rc;
    }
    return tcp_output(npcb);
  }
  return ERR_OK;
}

/**
 * Called by tcp_input() when a segment arrives for a connection in
 * TIME_WAIT.
 *
 * @param pcb the tcp_pcb for which a segment arrived
 *
 * @note the segment which arrived is saved in global variables, therefore only the pcb
 *       involved is passed as a parameter to this function
 */
/*处于TIME_WAIT状态的控制块调用tcp_timewait_input处理接受到的报文段，在该状态下，关闭连接的握手过程已经结束，
正在等待2MSL超时，在该状态下的报文段应该是连接中的旧数据，直接删除即可*/
static err_t
tcp_timewait_input(struct tcp_pcb *pcb)
{
  /* RFC 1337: in TIME_WAIT, ignore RST and ACK FINs + any 'acceptable' segments */
  /* RFC 793 3.9 Event Processing - Segment Arrives:
   * - first check sequence number - we skip that one in TIME_WAIT (always
   *   acceptable since we only send ACKs)
   * - second check the RST bit (... return) */
  if (flags & TCP_RST)  {   /*若报文的RST置位，直接返回*/
    return ERR_OK;
  }
  /* - fourth, check the SYN bit, */
  if (flags & TCP_SYN) {   /*若报文段包含了SYN握手信息，且握手数据编号在接收窗口内，则向对方发送RST报文*/
    /* If an incoming segment is not acceptable, an acknowledgment
       should be sent in reply */
    if (TCP_SEQ_BETWEEN(seqno, pcb->rcv_nxt, pcb->rcv_nxt+pcb->rcv_wnd)) {
      /* If the SYN is in the window it is an error, send a reset */
      tcp_rst(ackno, seqno + tcplen, ip_current_dest_addr(), ip_current_src_addr(),
        tcphdr->dest, tcphdr->src);
      return ERR_OK;
    }
  } else if (flags & TCP_FIN) {   /*若报文段包含了FIN握手信息，复位2MSL等待时间，控制块重新等待2MSL*/
    /* - eighth, check the FIN bit: Remain in the TIME-WAIT state.
         Restart the 2 MSL time-wait timeout.*/
    pcb->tmr = tcp_ticks;
  }

  if ((tcplen > 0))  {  /*对于有数据的报文，或者在接收窗口外的SYN报文发送一个ACK报文段*/
    /* Acknowledge data, FIN or out-of-window SYN */
    pcb->flags |= TF_ACK_NOW;
    return tcp_output(pcb);
  }
  return ERR_OK;
}

/**
 * Implements the TCP state machine. Called by tcp_input. In some
 * states tcp_receive() is called to receive data. The tcp_seg
 * argument will be freed by the caller (tcp_input()) unless the
 * recv_data pointer in the pcb is set.
 *
 * @param pcb the tcp_pcb for which a segment arrived
 *
 * @note the segment which arrived is saved in global variables, therefore only the pcb
 *       involved is passed as a parameter to this function
 */
static err_t
tcp_process(struct tcp_pcb *pcb)
{
  struct tcp_seg *rseg;
  u8_t acceptable = 0;
  err_t err;

  err = ERR_OK;

  /* Process incoming RST segments. */
  /*判断收到的报文段RST标志置位，则判断该报文段是否合法，若合法，则复位当前的连接*/
  if (flags & TCP_RST) {
    /* First, determine if the reset is acceptable. */
    if (pcb->state == SYN_SENT) {  /*第一种情况，连接处于SYN_SENT状态，且报文中确认号与snd_nxt相等*/
      if (ackno == pcb->snd_nxt) {
        acceptable = 1;
      }
    } else {        /*其他状态下报文中序列号在接收窗口内*/
      if (TCP_SEQ_BETWEEN(seqno, pcb->rcv_nxt, 
                          pcb->rcv_nxt+pcb->rcv_wnd)) {
        acceptable = 1;
      }
    }
/*如果复位合法，则需要复位当前连接的控制块*/
    if (acceptable) {
      LWIP_DEBUGF(TCP_INPUT_DEBUG, ("tcp_process: Connection RESET\n"));
      LWIP_ASSERT("tcp_input: pcb->state != CLOSED", pcb->state != CLOSED);
      recv_flags |= TF_RESET;    /*设置recv_flag为复位，tcp_input将删除控制块*/
      pcb->flags &= ~TF_ACK_DELAY;
      return ERR_RST;/*返回*/
    } else {/*复位报文不合法，直接返回，不对报文做处理*/
      LWIP_DEBUGF(TCP_INPUT_DEBUG, ("tcp_process: unacceptable reset seqno %"U32_F" rcv_nxt %"U32_F"\n",
       seqno, pcb->rcv_nxt));
      LWIP_DEBUGF(TCP_DEBUG, ("tcp_process: unacceptable reset seqno %"U32_F" rcv_nxt %"U32_F"\n",
       seqno, pcb->rcv_nxt));
      return ERR_OK;
    }
  }
/*可能是一个超市重发的握手包，直接向对方返回ACK即可*/
  if ((flags & TCP_SYN) && (pcb->state != SYN_SENT && pcb->state != SYN_RCVD)) { 
    /* Cope with new connection attempt after remote end crashed */
    tcp_ack_now(pcb);
    return ERR_OK;
  }
  
  if ((pcb->flags & TF_RXCLOSED) == 0) {
    /* Update the PCB (in)activity timer unless rx is closed (see tcp_shutdown) */
    pcb->tmr = tcp_ticks;/*复位控制块的活动计数器*/
  }
  pcb->keep_cnt_sent = 0;/*保活报文计数器清0（保活机制）*/

  tcp_parseopt(pcb);/*处理报文首部中的选项字段，设置控制块中的flags标志*/

  /* Do different things depending on the TCP state. */
  /*以下是实现TCP状态机的具体部分*/
  switch (pcb->state) {
  case SYN_SENT:   /*客户端发送SYN后，处于该状态等待服务器返回SYN+ACK*/
    LWIP_DEBUGF(TCP_INPUT_DEBUG, ("SYN-SENT: ackno %"U32_F" pcb->snd_nxt %"U32_F" unacked %"U32_F"\n", ackno,
     pcb->snd_nxt, ntohl(pcb->unacked->tcphdr->seqno)));
    /* received SYN ACK with expected sequence number? */
    if ((flags & TCP_ACK) && (flags & TCP_SYN)      /*是SYN+ACK，且序列号正确，SYN被确认，该报文占用一个字节，可用空间加上1字节*/
        && ackno == ntohl(pcb->unacked->tcphdr->seqno) + 1) {
      pcb->snd_buf++;
      pcb->rcv_nxt = seqno + 1;   /*设置接收序列号*/
      pcb->rcv_ann_right_edge = pcb->rcv_nxt;  /*初始化通告窗口的右边边界值*/
      pcb->lastack = ackno;   /*被确认的最高序号*/
      pcb->snd_wnd = tcphdr->wnd;/*发送窗口设置为接收窗口*/
    /*snd_wl1设置为sepno-1，在收到对方有效窗口通告后会迫使发送窗口更新*/
      pcb->snd_wl1 = seqno - 1; /* initialise to seqno - 1 to force window update */
      pcb->state = ESTABLISHED; /*进入ESTABLISHED状态*/

#if TCP_CALCULATE_EFF_SEND_MSS
      pcb->mss = tcp_eff_send_mss(pcb->mss, &(pcb->remote_ip));   /*设置最大报文段*/
#endif /* TCP_CALCULATE_EFF_SEND_MSS */

      /* Set ssthresh again after changing pcb->mss (already set in tcp_connect
       * but for the default value of pcb->mss) */
      pcb->ssthresh = pcb->mss * 10;

      pcb->cwnd = ((pcb->cwnd == 1) ? (pcb->mss * 2) : pcb->mss);   /*初始化阻塞窗口*/
      LWIP_ASSERT("pcb->snd_queuelen > 0", (pcb->snd_queuelen > 0));
      --pcb->snd_queuelen;    /*SYN报文被确认，占用pbuf个数减1*/
      LWIP_DEBUGF(TCP_QLEN_DEBUG, ("tcp_process: SYN-SENT --queuelen %"U16_F"\n", (u16_t)pcb->snd_queuelen));
      rseg = pcb->unacked;  /*在缓存队列中删除报文*/
      pcb->unacked = rseg->next;

      /* If there's nothing left to acknowledge, stop the retransmit
         timer, otherwise reset it to start again */
      if(pcb->unacked == NULL)    /*未确认队列为空，则停止重传计数器*/
        pcb->rtime = -1;
      else {            /*队列上有报文，则复位重传计数器、重传次数*/
        pcb->rtime = 0;
        pcb->nrtx = 0;
      }

      tcp_seg_free(rseg);   /*释放取下的SYN报文段空间*/

      /* Call the user specified function to call when sucessfully
       * connected. */
      TCP_EVENT_CONNECTED(pcb, ERR_OK, err);    /*回调用户的connected函数，*/
      if (err == ERR_ABRT) {
        return ERR_ABRT;
      }
      tcp_ack_now(pcb);/*向服务器返回ACK，三次握手结束*/
    }
    /* received ACK? possibly a half-open connection */
    else if (flags & TCP_ACK) {     /*只收到对方的ACK却没有SYN，则向对方返回RST*/
      /* send a RST to bring the other side in a non-synchronized state. */
      tcp_rst(ackno, seqno + tcplen, ip_current_dest_addr(), ip_current_src_addr(), /*不知此版打开状态*/
        tcphdr->dest, tcphdr->src);
    }
    break;
  case SYN_RCVD:    /*服务器发送完SYN+ACK后，将处于该状态*/
    if (flags & TCP_ACK) {    /*收到ACK报文，三次握手的最后一个报文*/
      /* expected ACK number? */
      if (TCP_SEQ_BETWEEN(ackno, pcb->lastack+1, pcb->snd_nxt)) {    /*确认号合法*/
        u16_t old_cwnd;
        pcb->state = ESTABLISHED;     /*进入ESTABILISHED状态*/
        LWIP_DEBUGF(TCP_DEBUG, ("TCP connection established %"U16_F" -> %"U16_F".\n", inseg.tcphdr->src, inseg.tcphdr->dest));
#if LWIP_CALLBACK_API
        LWIP_ASSERT("pcb->accept != NULL", pcb->accept != NULL);
#endif
        /* Call the accept function. */
        TCP_EVENT_ACCEPT(pcb, ERR_OK, err);/*回调用户的accept函数*/
        if (err != ERR_OK) {                  /*如果accept回调函数执行错误，则关闭当前连接*/
          /* If the accept function returns with an error, we abort
           * the connection. */
          /* Already aborted? */
          if (err != ERR_ABRT) {
            tcp_abort(pcb);
          }
          return ERR_ABRT;   /*返回错误*/
        }
        old_cwnd = pcb->cwnd;    /*依旧保持旧的阻塞窗口*/
        /* If there was any data contained within this ACK,
         * we'd better pass it on to the application as well. */

        /*调用函数处理报文中的数据*/
        tcp_receive(pcb);

        /* Prevent ACK for SYN to generate a sent event */
        if (pcb->acked != 0) {       /*如果本地有未确认数据被报文中的ACK确认*/
          pcb->acked--;     /*调整确认的字节数，因为SYN报文占了一个字节*/
        }

        pcb->cwnd = ((old_cwnd == 1) ? (pcb->mss * 2) : pcb->mss);/*重新设置阻塞窗口*/

        if (recv_flags & TF_GOT_FIN) {    /*tcp_receive处理时设置了关闭连接标志*/
          tcp_ack_now(pcb);   /*响应对方的FIN握手标志*/
          pcb->state = CLOSE_WAIT;  /*进入CLOSE_WAIT状态*/
        }
      } else {    /*不合法ACK序号则返回一个复位报文*/
        /* incorrect ACK number, send RST */
        tcp_rst(ackno, seqno + tcplen, ip_current_dest_addr(), ip_current_src_addr(),
                tcphdr->dest, tcphdr->src);
      }
    } else if ((flags & TCP_SYN) && (seqno == pcb->rcv_nxt - 1)) { /*收到对方的重复的SYN握手，说明SYN+ACK丢失，这里重传SYN+ACK*/
      /* Looks like another copy of the SYN - retransmit our SYN-ACK */
      tcp_rexmit(pcb);
    }
    break;
  case CLOSE_WAIT:/*服务器处于半关闭状态，不可能在接收到来自客户端的报文，服务器在此状态下会一直等待上上层应用执行关闭命令tcp_close*/
    /* FALLTHROUGH */
  case ESTABLISHED:   /*连接双方都处于稳定状态*/
    tcp_receive(pcb);   /*调用函数处理文中的数据*/
    if (recv_flags & TF_GOT_FIN) { /* passive close *//*tcp_receive处理时设置了关闭连接标志*/
      tcp_ack_now(pcb);   /*响应对方的FIN握手标志*/
      pcb->state = CLOSE_WAIT;   /*进入CLOSE_WAIT状态*/
    }
    break;
  case FIN_WAIT_1: /*上次应用调用tcp_close关闭连接，发送FIN后处于该状态 */
    tcp_receive(pcb);      /*调用函数处理报文中的数据*/
    if (recv_flags & TF_GOT_FIN) {    /*收到对方的FIN握手*/              /*=====特殊状态=====*/
      if ((flags & TCP_ACK) && (ackno == pcb->snd_nxt)) { /*且包含有效的ACK*/
        LWIP_DEBUGF(TCP_DEBUG,
          ("TCP connection closed: FIN_WAIT_1 %"U16_F" -> %"U16_F".\n", inseg.tcphdr->src, inseg.tcphdr->dest));
        tcp_ack_now(pcb);         /*发送ACK*/
        tcp_pcb_purge(pcb);       /*清除连接中的所有现存数据*/
        TCP_RMV(&tcp_active_pcbs, pcb); /*从tcp_active_pcbs链表中删除*/
        pcb->state = TIME_WAIT;        /*设置为TIME_WAIT状态*/ 
        TCP_REG(&tcp_tw_pcbs, pcb);    /*加入tcp_tw_pcbs链表*/
      } else {                       /*双方同时执行关闭操作*/
        tcp_ack_now(pcb);     /*返回ACK*/
        pcb->state = CLOSING;    /*进入CLOSING'状态*/
      }
    } else if ((flags & TCP_ACK) && (ackno == pcb->snd_nxt)) {   /*只收到有效ACK*/
      pcb->state = FIN_WAIT_2;                                /*进入FIN—WAIT状态*/
    }
    break;
  case FIN_WAIT_2:    /*主动关闭，发送FIN握手且接收到ACK后处于该状态*/
    tcp_receive(pcb);             /*调用函数处理报文中的数据*/
    if (recv_flags & TF_GOT_FIN) {      /*接收到对方的FIN握手*/
      LWIP_DEBUGF(TCP_DEBUG, ("TCP connection closed: FIN_WAIT_2 %"U16_F" -> %"U16_F".\n", inseg.tcphdr->src, inseg.tcphdr->dest));
      tcp_ack_now(pcb);       /*发送ACK*/
      tcp_pcb_purge(pcb);     /*清除该连接上的所有现存数据*/
      TCP_RMV(&tcp_active_pcbs, pcb);    /*从tcp_active)pcbs链表中删除*/
      pcb->state = TIME_WAIT;       /*置位TIME_WAIT状态*/
      TCP_REG(&tcp_tw_pcbs, pcb);    /*加入tcp_tw_pcbs链表*/
    }
    break;
  case CLOSING:    /*双方同时执行主动关闭，处于该状态*/               /*========特殊状态======*/
    tcp_receive(pcb);
    if (flags & TCP_ACK && ackno == pcb->snd_nxt) {      /*收到有效ACK*/
      LWIP_DEBUGF(TCP_DEBUG, ("TCP connection closed: CLOSING %"U16_F" -> %"U16_F".\n", inseg.tcphdr->src, inseg.tcphdr->dest));
      tcp_pcb_purge(pcb);
      TCP_RMV(&tcp_active_pcbs, pcb);
      pcb->state = TIME_WAIT;
      TCP_REG(&tcp_tw_pcbs, pcb);
    }
    break;
  case LAST_ACK:      /*服务器正在执行被动关闭时，发送完FIN，等待ACK返回*/
    tcp_receive(pcb);
    if (flags & TCP_ACK && ackno == pcb->snd_nxt) {       /*收到有效ACK*/
      LWIP_DEBUGF(TCP_DEBUG, ("TCP connection closed: LAST_ACK %"U16_F" -> %"U16_F".\n", inseg.tcphdr->src, inseg.tcphdr->dest));
      /* bugfix #21699: don't set pcb->state to CLOSED here or we risk leaking segments */
      recv_flags |= TF_CLOSED;  /*设置recv_flags为TF_CLOSE，由tcp_input函数，对该控制块进行释放和清除工作*/
    }
    break;
  default:
    break;
  }
  return ERR_OK;
}

#if TCP_QUEUE_OOSEQ
/**
 * Insert segment into the list (segments covered with new one will be deleted)
 *
 * Called from tcp_receive()
 */
static void
tcp_oos_insert_segment(struct tcp_seg *cseg, struct tcp_seg *next)
{
  struct tcp_seg *old_seg;

  if (TCPH_FLAGS(cseg->tcphdr) & TCP_FIN) {
    /* received segment overlaps all following segments */
    tcp_segs_free(next);
    next = NULL;
  }
  else {
    /* delete some following segments
       oos queue may have segments with FIN flag */
    while (next &&
           TCP_SEQ_GEQ((seqno + cseg->len),
                      (next->tcphdr->seqno + next->len))) {
      /* cseg with FIN already processed */
      if (TCPH_FLAGS(next->tcphdr) & TCP_FIN) {
        TCPH_SET_FLAG(cseg->tcphdr, TCP_FIN);
      }
      old_seg = next;
      next = next->next;
      tcp_seg_free(old_seg);
    }
    if (next &&
        TCP_SEQ_GT(seqno + cseg->len, next->tcphdr->seqno)) {
      /* We need to trim the incoming segment. */
      cseg->len = (u16_t)(next->tcphdr->seqno - seqno);
      pbuf_realloc(cseg->p, cseg->len);
    }
  }
  cseg->next = next;
}
#endif /* TCP_QUEUE_OOSEQ */

/**
 * Called by tcp_process. Checks if the given segment is an ACK for outstanding
 * data, and if so frees the memory of the buffered data. Next, is places the
 * segment on any of the receive queues (pcb->recved or pcb->ooseq). If the segment
 * is buffered, the pbuf is referenced by pbuf_ref so that it will not be freed until
 * i it has been removed from the buffer.
 *
 * If the incoming segment constitutes an ACK for a segment that was used for RTT
 * estimation, the RTT is estimated here as well.
 *
 * Called from tcp_process().
 */
/*函数实现：首先检查报文中携带的确认号是否确认了未确认的队列unacked中的数据，如果是，
则释放掉被确认的数据空间，并设置acked字段值以便tcp_input回调用户函数，
同时，如果报文段中有数据且数据有序，这些数据会被记录在recv_data中，
以便用户程序处理；如果控制块的oose队列上的报文段因为新报文段的到来而变得有序，则这些
报文段的数据也会被一起连接在recv_data中，在函数退出后由tcp_input递交给应用程序处理；
如果新报文段不是有序的，则报文段将为插到队列ooseq上，该报文段的引用指针将被加1.
防止在其他地方被删除。最后，还有很多其他工作也需要在该函数中完成，列如当前确认号
包含了对正在进行RTT估计的报文的确认，则RTT需要被计算；如果收到重复的ACK，
这可能在函数中启动快重传算法等*/

/*        
             --------       -----------
          (2)|5|6|7|8|  (4)|11|12|13|14|
              --------      -----------    
       ---------   ----------           ----------- 
    (1) 2|3|4|5|(3) 7|8|9|10|       (5)|15|16|17|18|  
        --------   ----------           -----------
     -----------------------------------------
      ....|3|4|5|6|7|8|9|10|11|12|13|14|15|.....    
     -----------------------------------------
          |-------rcv_nxt-----------|
          |--------rcv_wnd----------|


1.如果数据起始编号seqno并不恰恰是rcv_nxt，而是比rcv_nxt小，同时数据段中又有数据编号是rcv_nxt，此时需要将数据段截断，
使其起始编号恰恰是rcv_nxt，如（2）     若seqno小于rcv_nxt，且报文段中所有数据的编号均小于rcv_nxt，说明这是一个重复的报文
，对这类重复报文段只是响应一个ACK报文给源端，不做其他处理，如（1）
*/

static void
tcp_receive(struct tcp_pcb *pcb)
{
  struct tcp_seg *next;
#if TCP_QUEUE_OOSEQ
  struct tcp_seg *prev, *cseg;
#endif /* TCP_QUEUE_OOSEQ */
  struct pbuf *p;
  s32_t off;
  s16_t m;
  u32_t right_wnd_edge;
  u16_t new_tot_len;
  int found_dupack = 0;

  if (flags & TCP_ACK) {/*包含ACK*/
    right_wnd_edge = pcb->snd_wnd + pcb->snd_wl2;

    /* Update window. */
    /*
    （1）新seqno大于snd_wl1  连接建立的握手过程中就使用这种方式更新窗口
    （2）新seqno等于snd_wl1且新确认号ackno大于snd_wl2   说明对方没有发送数据，只是在接收到数据之后发送一个确认号
    （3）新确认号等于snd_wl2且报文首部有比snd_wnd更大的窗口通告
       更新窗口：重新设置snd_wnd  sdn_wl1   snd_wl2
    */
    if (TCP_SEQ_LT(pcb->snd_wl1, seqno) ||
       (pcb->snd_wl1 == seqno && TCP_SEQ_LT(pcb->snd_wl2, ackno)) ||
       (pcb->snd_wl2 == ackno && tcphdr->wnd > pcb->snd_wnd)) {
      pcb->snd_wnd = tcphdr->wnd;
      pcb->snd_wl1 = seqno;
      pcb->snd_wl2 = ackno;
      if (pcb->snd_wnd > 0 && pcb->persist_backoff > 0) {
          pcb->persist_backoff = 0;
      }
      LWIP_DEBUGF(TCP_WND_DEBUG, ("tcp_receive: window update %"U16_F"\n", pcb->snd_wnd));
#if TCP_WND_DEBUG
    } else {
      if (pcb->snd_wnd != tcphdr->wnd) {
        LWIP_DEBUGF(TCP_WND_DEBUG, 
                    ("tcp_receive: no window update lastack %"U32_F" ackno %"
                     U32_F" wl1 %"U32_F" seqno %"U32_F" wl2 %"U32_F"\n",
                     pcb->lastack, ackno, pcb->snd_wl1, seqno, pcb->snd_wl2));
      }
#endif /* TCP_WND_DEBUG */
    }

    /* (From Stevens TCP/IP Illustrated Vol II, p970.) Its only a
     * duplicate ack if:
     * 1) It doesn't ACK new data 
     * 2) length of received packet is zero (i.e. no payload) 
     * 3) the advertised window hasn't changed 
     * 4) There is outstanding unacknowledged data (retransmission timer running)
     * 5) The ACK is == biggest ACK sequence number so far seen (snd_una)
     * 
     * If it passes all five, should process as a dupack: 
     * a) dupacks < 3: do nothing 
     * b) dupacks == 3: fast retransmit 
     * c) dupacks > 3: increase cwnd 
     * 
     * If it only passes 1-3, should reset dupack counter (and add to
     * stats, which we don't do in lwIP)
     
     * If it only passes 1, should reset dupack counter
     *
     */

    /* Clause 1 */
    if (TCP_SEQ_LEQ(ackno, pcb->lastack)) {
      pcb->acked = 0;  /*没有确认新数据*/
      /* Clause 2 */
      if (tcplen == 0) {   /*报文段中没有任何数据，也不包含SYN、FIN*/
        /* Clause 3 */
        if (pcb->snd_wl2 + pcb->snd_wnd == right_wnd_edge){   /*在（1）的窗口更新过程中，本地发送窗口没有跟新*/
          /* Clause 4 */
          if (pcb->rtime >= 0) {    /*本地任然有数据正等待被确认*/
            /* Clause 5 */
            if (pcb->lastack == ackno) {      /*ackno等于lastack，确认号等于最高确认号*/
              found_dupack = 1;     /*设置重复ACK标志*/
              if (pcb->dupacks + 1 > pcb->dupacks)/*更新控制块中的dupacks字段*/
                ++pcb->dupacks;/**/
              if (pcb->dupacks > 3) {   /*若处于快速恢复与快速重传阶段*/
                /* Inflate the congestion window, but not if it means that
                   the value overflows. */
                if ((u16_t)(pcb->cwnd + pcb->mss) > pcb->cwnd) {   /*快速恢复算法*/
                  pcb->cwnd += pcb->mss;    /*将cwnd增加一个报文段大小*/
                }
              } else if (pcb->dupacks == 3) {   /*此时收到三次重复ACK，执行快速重传*/
                /* Do fast retransmit */
                tcp_rexmit_fast(pcb);/*快速重传，初始化cwnd与ssthresh/
              }
            }
          }
        }
      }
      /* If Clause (1) or more is true, but not a duplicate ack, reset
       * count of consecutive duplicate acks */
      if (!found_dupack) {
        pcb->dupacks = 0;
      }
    } else if (TCP_SEQ_BETWEEN(ackno, pcb->lastack+1, pcb->snd_nxt)){/*ack确认了数据*/
      /* We come here when the ACK acknowledges new data. */

      /* Reset the "IN Fast Retransmit" flag, since we are no longer
         in fast retransmit. Also reset the congestion window to the
         slow start threshold.*/
      if (pcb->flags & TF_INFR) {
        pcb->flags &= ~TF_INFR;
        pcb->cwnd = pcb->ssthresh;
      }

      /* Reset the number of retransmissions.*/
      pcb->nrtx = 0;

      /* Reset the retransmission time-out. */
      pcb->rto = (pcb->sa >> 3) + pcb->sv;

      /* Update the send buffer space. Diff between the two can never exceed 64K? */
      pcb->acked = (u16_t)(ackno - pcb->lastack);

      pcb->snd_buf += pcb->acked;

      /* Reset the fast retransmit variables. */
      pcb->dupacks = 0;
      pcb->lastack = ackno;

      /* Update the congestion control variables (cwnd and
         ssthresh). */
      if (pcb->state >= ESTABLISHED) {
        if (pcb->cwnd < pcb->ssthresh) {
          if ((u16_t)(pcb->cwnd + pcb->mss) > pcb->cwnd) {/*慢启动阶段*/
            pcb->cwnd += pcb->mss;
          }
          LWIP_DEBUGF(TCP_CWND_DEBUG, ("tcp_receive: slow start cwnd %"U16_F"\n", pcb->cwnd));
        } else {
          u16_t new_cwnd = (pcb->cwnd + pcb->mss * pcb->mss / pcb->cwnd);/*拥塞避免阶段*/
          if (new_cwnd > pcb->cwnd) {
            pcb->cwnd = new_cwnd;
          }
          LWIP_DEBUGF(TCP_CWND_DEBUG, ("tcp_receive: congestion avoidance cwnd %"U16_F"\n", pcb->cwnd));
        }
      }
      LWIP_DEBUGF(TCP_INPUT_DEBUG, ("tcp_receive: ACK for %"U32_F", unacked->seqno %"U32_F":%"U32_F"\n",
                                    ackno,
                                    pcb->unacked != NULL?
                                    ntohl(pcb->unacked->tcphdr->seqno): 0,
                                    pcb->unacked != NULL?
                                    ntohl(pcb->unacked->tcphdr->seqno) + TCP_TCPLEN(pcb->unacked): 0));

      /* Remove segment from the unacknowledged list if the incoming
         ACK acknowlegdes them. */
      while (pcb->unacked != NULL &&
             TCP_SEQ_LEQ(ntohl(pcb->unacked->tcphdr->seqno) +
                         TCP_TCPLEN(pcb->unacked), ackno)) {
        LWIP_DEBUGF(TCP_INPUT_DEBUG, ("tcp_receive: removing %"U32_F":%"U32_F" from pcb->unacked\n",
                                      ntohl(pcb->unacked->tcphdr->seqno),
                                      ntohl(pcb->unacked->tcphdr->seqno) +
                                      TCP_TCPLEN(pcb->unacked)));

        next = pcb->unacked;
        pcb->unacked = pcb->unacked->next;

        LWIP_DEBUGF(TCP_QLEN_DEBUG, ("tcp_receive: queuelen %"U16_F" ... ", (u16_t)pcb->snd_queuelen));
        LWIP_ASSERT("pcb->snd_queuelen >= pbuf_clen(next->p)", (pcb->snd_queuelen >= pbuf_clen(next->p)));
        /* Prevent ACK for FIN to generate a sent event */
        if ((pcb->acked != 0) && ((TCPH_FLAGS(next->tcphdr) & TCP_FIN) != 0)) {
          pcb->acked--;
        }

        pcb->snd_queuelen -= pbuf_clen(next->p);
        tcp_seg_free(next);

        LWIP_DEBUGF(TCP_QLEN_DEBUG, ("%"U16_F" (after freeing unacked)\n", (u16_t)pcb->snd_queuelen));
        if (pcb->snd_queuelen != 0) {
          LWIP_ASSERT("tcp_receive: valid queue length", pcb->unacked != NULL ||
                      pcb->unsent != NULL);
        }
      }

      /* If there's nothing left to acknowledge, stop the retransmit
         timer, otherwise reset it to start again */
      if(pcb->unacked == NULL)    /*无数据等待确认*/
        pcb->rtime = -1;     /*停止重传计数器*/
      else
        pcb->rtime = 0;   /*复位计数器*/

      pcb->polltmr = 0;
    } else {
      /* Fix bug bug #21582: out of sequence ACK, didn't really ack anything */
      pcb->acked = 0;
    }

    /* We go through the ->unsent list to see if any of the segments
       on the list are acknowledged by the ACK. This may seem
       strange since an "unsent" segment shouldn't be acked. The
       rationale is that lwIP puts all outstanding segments on the
       ->unsent list after a retransmission, so these segments may
       in fact have been sent once. */
    while (pcb->unsent != NULL &&
           TCP_SEQ_BETWEEN(ackno, ntohl(pcb->unsent->tcphdr->seqno) + 
                           TCP_TCPLEN(pcb->unsent), pcb->snd_nxt)) {
      LWIP_DEBUGF(TCP_INPUT_DEBUG, ("tcp_receive: removing %"U32_F":%"U32_F" from pcb->unsent\n",
                                    ntohl(pcb->unsent->tcphdr->seqno), ntohl(pcb->unsent->tcphdr->seqno) +
                                    TCP_TCPLEN(pcb->unsent)));

      next = pcb->unsent;
      pcb->unsent = pcb->unsent->next;
      LWIP_DEBUGF(TCP_QLEN_DEBUG, ("tcp_receive: queuelen %"U16_F" ... ", (u16_t)pcb->snd_queuelen));
      LWIP_ASSERT("pcb->snd_queuelen >= pbuf_clen(next->p)", (pcb->snd_queuelen >= pbuf_clen(next->p)));
      /* Prevent ACK for FIN to generate a sent event */
      if ((pcb->acked != 0) && ((TCPH_FLAGS(next->tcphdr) & TCP_FIN) != 0)) {
        pcb->acked--;
      }
      pcb->snd_queuelen -= pbuf_clen(next->p);
      tcp_seg_free(next);
      LWIP_DEBUGF(TCP_QLEN_DEBUG, ("%"U16_F" (after freeing unsent)\n", (u16_t)pcb->snd_queuelen));
      if (pcb->snd_queuelen != 0) {
        LWIP_ASSERT("tcp_receive: valid queue length",
          pcb->unacked != NULL || pcb->unsent != NULL);
      }
    }
    /* End of ACK for new data processing. */

    LWIP_DEBUGF(TCP_RTO_DEBUG, ("tcp_receive: pcb->rttest %"U32_F" rtseq %"U32_F" ackno %"U32_F"\n",
                                pcb->rttest, pcb->rtseq, ackno));

    /* RTT estimation calculations. This is done by checking if the
       incoming segment acknowledges the segment we use to take a
       round-trip time measurement. */
    if (pcb->rttest && TCP_SEQ_LT(pcb->rtseq, ackno)) {
      /* diff between this shouldn't exceed 32K since this are tcp timer ticks
         and a round-trip shouldn't be that long... */
      m = (s16_t)(tcp_ticks - pcb->rttest);

      LWIP_DEBUGF(TCP_RTO_DEBUG, ("tcp_receive: experienced rtt %"U16_F" ticks (%"U16_F" msec).\n",
                                  m, m * TCP_SLOW_INTERVAL));

      /* This is taken directly from VJs original code in his paper */
      m = m - (pcb->sa >> 3);
      pcb->sa += m;
      if (m < 0) {
        m = -m;
      }
      m = m - (pcb->sv >> 2);
      pcb->sv += m;
      pcb->rto = (pcb->sa >> 3) + pcb->sv;

      LWIP_DEBUGF(TCP_RTO_DEBUG, ("tcp_receive: RTO %"U16_F" (%"U16_F" milliseconds)\n",
                                  pcb->rto, pcb->rto * TCP_SLOW_INTERVAL));

      pcb->rttest = 0;
    }
  }

  /* If the incoming segment contains data, we must process it
     further. */
  if (tcplen > 0) {
    /* This code basically does three things:

    +) If the incoming segment contains data that is the next
    in-sequence data, this data is passed to the application. This
    might involve trimming the first edge of the data. The rcv_nxt
    variable and the advertised window are adjusted.

    +) If the incoming segment has data that is above the next
    sequence number expected (->rcv_nxt), the segment is placed on
    the ->ooseq queue. This is done by finding the appropriate
    place in the ->ooseq queue (which is ordered by sequence
    number) and trim the segment in both ends if needed. An
    immediate ACK is sent to indicate that we received an
    out-of-sequence segment.

    +) Finally, we check if the first segment on the ->ooseq queue
    now is in sequence (i.e., if rcv_nxt >= ooseq->seqno). If
    rcv_nxt > ooseq->seqno, we must trim the first edge of the
    segment on ->ooseq before we adjust rcv_nxt. The data in the
    segments that are now on sequence are chained onto the
    incoming segment so that we only need to call the application
    once.
    */

    /* First, we check if we must trim the first edge. We have to do
       this if the sequence number of the incoming segment is less
       than rcv_nxt, and the sequence number plus the length of the
       segment is larger than rcv_nxt. */
    /*    if (TCP_SEQ_LT(seqno, pcb->rcv_nxt)){
          if (TCP_SEQ_LT(pcb->rcv_nxt, seqno + tcplen)) {*/
    if (TCP_SEQ_BETWEEN(pcb->rcv_nxt, seqno + 1, seqno + tcplen - 1)){
      /* Trimming the first edge is done by pushing the payload
         pointer in the pbuf downwards. This is somewhat tricky since
         we do not want to discard the full contents of the pbuf up to
         the new starting point of the data since we have to keep the
         TCP header which is present in the first pbuf in the chain.

         What is done is really quite a nasty hack: the first pbuf in
         the pbuf chain is pointed to by inseg.p. Since we need to be
         able to deallocate the whole pbuf, we cannot change this
         inseg.p pointer to point to any of the later pbufs in the
         chain. Instead, we point the ->payload pointer in the first
         pbuf to data in one of the later pbufs. We also set the
         inseg.data pointer to point to the right place. This way, the
         ->p pointer will still point to the first pbuf, but the
         ->p->payload pointer will point to data in another pbuf.

         After we are done with adjusting the pbuf pointers we must
         adjust the ->data pointer in the seg and the segment
         length.*/

      off = pcb->rcv_nxt - seqno;
      p = inseg.p;
      LWIP_ASSERT("inseg.p != NULL", inseg.p);
      LWIP_ASSERT("insane offset!", (off < 0x7fff));
      if (inseg.p->len < off) {
        LWIP_ASSERT("pbuf too short!", (((s32_t)inseg.p->tot_len) >= off));
        new_tot_len = (u16_t)(inseg.p->tot_len - off);
        while (p->len < off) {
          off -= p->len;
          /* KJM following line changed (with addition of new_tot_len var)
             to fix bug #9076
             inseg.p->tot_len -= p->len; */
          p->tot_len = new_tot_len;
          p->len = 0;
          p = p->next;
        }
        if(pbuf_header(p, (s16_t)-off)) {
          /* Do we need to cope with this failing?  Assert for now */
          LWIP_ASSERT("pbuf_header failed", 0);
        }
      } else {
        if(pbuf_header(inseg.p, (s16_t)-off)) {
          /* Do we need to cope with this failing?  Assert for now */
          LWIP_ASSERT("pbuf_header failed", 0);
        }
      }
      inseg.len -= (u16_t)(pcb->rcv_nxt - seqno);
      inseg.tcphdr->seqno = seqno = pcb->rcv_nxt;
    }
    else {
      if (TCP_SEQ_LT(seqno, pcb->rcv_nxt)){
        /* the whole segment is < rcv_nxt */
        /* must be a duplicate of a packet that has already been correctly handled */

        LWIP_DEBUGF(TCP_INPUT_DEBUG, ("tcp_receive: duplicate seqno %"U32_F"\n", seqno));
        tcp_ack_now(pcb);
      }
    }

    /* The sequence number must be within the window (above rcv_nxt
       and below rcv_nxt + rcv_wnd) in order to be further
       processed. */
    if (TCP_SEQ_BETWEEN(seqno, pcb->rcv_nxt, 
                        pcb->rcv_nxt + pcb->rcv_wnd - 1)){
      if (pcb->rcv_nxt == seqno) {
        /* The incoming segment is the next in sequence. We check if
           we have to trim the end of the segment and update rcv_nxt
           and pass the data to the application. */
        tcplen = TCP_TCPLEN(&inseg);

        if (tcplen > pcb->rcv_wnd) {
          LWIP_DEBUGF(TCP_INPUT_DEBUG, 
                      ("tcp_receive: other end overran receive window"
                       "seqno %"U32_F" len %"U16_F" right edge %"U32_F"\n",
                       seqno, tcplen, pcb->rcv_nxt + pcb->rcv_wnd));
          if (TCPH_FLAGS(inseg.tcphdr) & TCP_FIN) {
            /* Must remove the FIN from the header as we're trimming 
             * that byte of sequence-space from the packet */
            TCPH_FLAGS_SET(inseg.tcphdr, TCPH_FLAGS(inseg.tcphdr) &~ TCP_FIN);
          }
          /* Adjust length of segment to fit in the window. */
          inseg.len = pcb->rcv_wnd;
          if (TCPH_FLAGS(inseg.tcphdr) & TCP_SYN) {
            inseg.len -= 1;
          }
          pbuf_realloc(inseg.p, inseg.len);
          tcplen = TCP_TCPLEN(&inseg);
          LWIP_ASSERT("tcp_receive: segment not trimmed correctly to rcv_wnd\n",
                      (seqno + tcplen) == (pcb->rcv_nxt + pcb->rcv_wnd));
        }
#if TCP_QUEUE_OOSEQ
        /* Received in-sequence data, adjust ooseq data if:
           - FIN has been received or
           - inseq overlaps with ooseq */
        if (pcb->ooseq != NULL) {
          if (TCPH_FLAGS(inseg.tcphdr) & TCP_FIN) {
            LWIP_DEBUGF(TCP_INPUT_DEBUG, 
                        ("tcp_receive: received in-order FIN, binning ooseq queue\n"));
            /* Received in-order FIN means anything that was received
             * out of order must now have been received in-order, so
             * bin the ooseq queue */
            while (pcb->ooseq != NULL) {
              struct tcp_seg *old_ooseq = pcb->ooseq;
              pcb->ooseq = pcb->ooseq->next;
              tcp_seg_free(old_ooseq);
            }
          }
          else {
            next = pcb->ooseq;
            /* Remove all segments on ooseq that are covered by inseg already.
             * FIN is copied from ooseq to inseg if present. */
            while (next &&
                   TCP_SEQ_GEQ(seqno + tcplen,
                               next->tcphdr->seqno + next->len)) {
              /* inseg cannot have FIN here (already processed above) */
              if (TCPH_FLAGS(next->tcphdr) & TCP_FIN &&
                  (TCPH_FLAGS(inseg.tcphdr) & TCP_SYN) == 0) {
                TCPH_SET_FLAG(inseg.tcphdr, TCP_FIN);
                tcplen = TCP_TCPLEN(&inseg);
              }
              prev = next;
              next = next->next;
              tcp_seg_free(prev);
            }
            /* Now trim right side of inseg if it overlaps with the first
             * segment on ooseq */
            if (next &&
                TCP_SEQ_GT(seqno + tcplen,
                           next->tcphdr->seqno)) {
              /* inseg cannot have FIN here (already processed above) */
              inseg.len = (u16_t)(next->tcphdr->seqno - seqno);
              if (TCPH_FLAGS(inseg.tcphdr) & TCP_SYN) {
                inseg.len -= 1;
              }
              pbuf_realloc(inseg.p, inseg.len);
              tcplen = TCP_TCPLEN(&inseg);
              LWIP_ASSERT("tcp_receive: segment not trimmed correctly to ooseq queue\n",
                          (seqno + tcplen) == next->tcphdr->seqno);
            }
            pcb->ooseq = next;
          }
        }
#endif /* TCP_QUEUE_OOSEQ */

        pcb->rcv_nxt = seqno + tcplen;

        /* Update the receiver's (our) window. */
        LWIP_ASSERT("tcp_receive: tcplen > rcv_wnd\n", pcb->rcv_wnd >= tcplen);
        pcb->rcv_wnd -= tcplen;

        tcp_update_rcv_ann_wnd(pcb);

        /* If there is data in the segment, we make preparations to
           pass this up to the application. The ->recv_data variable
           is used for holding the pbuf that goes to the
           application. The code for reassembling out-of-sequence data
           chains its data on this pbuf as well.

           If the segment was a FIN, we set the TF_GOT_FIN flag that will
           be used to indicate to the application that the remote side has
           closed its end of the connection. */
        if (inseg.p->tot_len > 0) {
          recv_data = inseg.p;
          /* Since this pbuf now is the responsibility of the
             application, we delete our reference to it so that we won't
             (mistakingly) deallocate it. */
          inseg.p = NULL;
        }
        if (TCPH_FLAGS(inseg.tcphdr) & TCP_FIN) {
          LWIP_DEBUGF(TCP_INPUT_DEBUG, ("tcp_receive: received FIN.\n"));
          recv_flags |= TF_GOT_FIN;
        }

#if TCP_QUEUE_OOSEQ
        /* We now check if we have segments on the ->ooseq queue that
           are now in sequence. */
        while (pcb->ooseq != NULL &&
               pcb->ooseq->tcphdr->seqno == pcb->rcv_nxt) {

          cseg = pcb->ooseq;
          seqno = pcb->ooseq->tcphdr->seqno;

          pcb->rcv_nxt += TCP_TCPLEN(cseg);
          LWIP_ASSERT("tcp_receive: ooseq tcplen > rcv_wnd\n",
                      pcb->rcv_wnd >= TCP_TCPLEN(cseg));
          pcb->rcv_wnd -= TCP_TCPLEN(cseg);

          tcp_update_rcv_ann_wnd(pcb);

          if (cseg->p->tot_len > 0) {
            /* Chain this pbuf onto the pbuf that we will pass to
               the application. */
            if (recv_data) {
              pbuf_cat(recv_data, cseg->p);
            } else {
              recv_data = cseg->p;
            }
            cseg->p = NULL;
          }
          if (TCPH_FLAGS(cseg->tcphdr) & TCP_FIN) {
            LWIP_DEBUGF(TCP_INPUT_DEBUG, ("tcp_receive: dequeued FIN.\n"));
            recv_flags |= TF_GOT_FIN;
            if (pcb->state == ESTABLISHED) { /* force passive close or we can move to active close */
              pcb->state = CLOSE_WAIT;
            } 
          }

          pcb->ooseq = cseg->next;
          tcp_seg_free(cseg);
        }
#endif /* TCP_QUEUE_OOSEQ */


        /* Acknowledge the segment(s). */
        tcp_ack(pcb);

      } else {
        /* We get here if the incoming segment is out-of-sequence. */
        tcp_send_empty_ack(pcb);
#if TCP_QUEUE_OOSEQ
        /* We queue the segment on the ->ooseq queue. */
        if (pcb->ooseq == NULL) {
          pcb->ooseq = tcp_seg_copy(&inseg);
        } else {
          /* If the queue is not empty, we walk through the queue and
             try to find a place where the sequence number of the
             incoming segment is between the sequence numbers of the
             previous and the next segment on the ->ooseq queue. That is
             the place where we put the incoming segment. If needed, we
             trim the second edges of the previous and the incoming
             segment so that it will fit into the sequence.

             If the incoming segment has the same sequence number as a
             segment on the ->ooseq queue, we discard the segment that
             contains less data. */

          prev = NULL;
          for(next = pcb->ooseq; next != NULL; next = next->next) {
            if (seqno == next->tcphdr->seqno) {
              /* The sequence number of the incoming segment is the
                 same as the sequence number of the segment on
                 ->ooseq. We check the lengths to see which one to
                 discard. */
              if (inseg.len > next->len) {
                /* The incoming segment is larger than the old
                   segment. We replace some segments with the new
                   one. */
                cseg = tcp_seg_copy(&inseg);
                if (cseg != NULL) {
                  if (prev != NULL) {
                    prev->next = cseg;
                  } else {
                    pcb->ooseq = cseg;
                  }
                  tcp_oos_insert_segment(cseg, next);
                }
                break;
              } else {
                /* Either the lenghts are the same or the incoming
                   segment was smaller than the old one; in either
                   case, we ditch the incoming segment. */
                break;
              }
            } else {
              if (prev == NULL) {
                if (TCP_SEQ_LT(seqno, next->tcphdr->seqno)) {
                  /* The sequence number of the incoming segment is lower
                     than the sequence number of the first segment on the
                     queue. We put the incoming segment first on the
                     queue. */
                  cseg = tcp_seg_copy(&inseg);
                  if (cseg != NULL) {
                    pcb->ooseq = cseg;
                    tcp_oos_insert_segment(cseg, next);
                  }
                  break;
                }
              } else {
                /*if (TCP_SEQ_LT(prev->tcphdr->seqno, seqno) &&
                  TCP_SEQ_LT(seqno, next->tcphdr->seqno)) {*/
                if (TCP_SEQ_BETWEEN(seqno, prev->tcphdr->seqno+1, next->tcphdr->seqno-1)) {
                  /* The sequence number of the incoming segment is in
                     between the sequence numbers of the previous and
                     the next segment on ->ooseq. We trim trim the previous
                     segment, delete next segments that included in received segment
                     and trim received, if needed. */
                  cseg = tcp_seg_copy(&inseg);
                  if (cseg != NULL) {
                    if (TCP_SEQ_GT(prev->tcphdr->seqno + prev->len, seqno)) {
                      /* We need to trim the prev segment. */
                      prev->len = (u16_t)(seqno - prev->tcphdr->seqno);
                      pbuf_realloc(prev->p, prev->len);
                    }
                    prev->next = cseg;
                    tcp_oos_insert_segment(cseg, next);
                  }
                  break;
                }
              }
              /* If the "next" segment is the last segment on the
                 ooseq queue, we add the incoming segment to the end
                 of the list. */
              if (next->next == NULL &&
                  TCP_SEQ_GT(seqno, next->tcphdr->seqno)) {
                if (TCPH_FLAGS(next->tcphdr) & TCP_FIN) {
                  /* segment "next" already contains all data */
                  break;
                }
                next->next = tcp_seg_copy(&inseg);
                if (next->next != NULL) {
                  if (TCP_SEQ_GT(next->tcphdr->seqno + next->len, seqno)) {
                    /* We need to trim the last segment. */
                    next->len = (u16_t)(seqno - next->tcphdr->seqno);
                    pbuf_realloc(next->p, next->len);
                  }
                  /* check if the remote side overruns our receive window */
                  if ((u32_t)tcplen + seqno > pcb->rcv_nxt + (u32_t)pcb->rcv_wnd) {
                    LWIP_DEBUGF(TCP_INPUT_DEBUG, 
                                ("tcp_receive: other end overran receive window"
                                 "seqno %"U32_F" len %"U16_F" right edge %"U32_F"\n",
                                 seqno, tcplen, pcb->rcv_nxt + pcb->rcv_wnd));
                    if (TCPH_FLAGS(next->next->tcphdr) & TCP_FIN) {
                      /* Must remove the FIN from the header as we're trimming 
                       * that byte of sequence-space from the packet */
                      TCPH_FLAGS_SET(next->next->tcphdr, TCPH_FLAGS(next->next->tcphdr) &~ TCP_FIN);
                    }
                    /* Adjust length of segment to fit in the window. */
                    next->next->len = pcb->rcv_nxt + pcb->rcv_wnd - seqno;
                    pbuf_realloc(next->next->p, next->next->len);
                    tcplen = TCP_TCPLEN(next->next);
                    LWIP_ASSERT("tcp_receive: segment not trimmed correctly to rcv_wnd\n",
                                (seqno + tcplen) == (pcb->rcv_nxt + pcb->rcv_wnd));
                  }
                }
                break;
              }
            }
            prev = next;
          }
        }
#endif /* TCP_QUEUE_OOSEQ */

      }
    } else {
      /* The incoming segment is not withing the window. */
      tcp_send_empty_ack(pcb);
    }
  } else {
    /* Segments with length 0 is taken care of here. Segments that
       fall out of the window are ACKed. */
    /*if (TCP_SEQ_GT(pcb->rcv_nxt, seqno) ||
      TCP_SEQ_GEQ(seqno, pcb->rcv_nxt + pcb->rcv_wnd)) {*/
    if(!TCP_SEQ_BETWEEN(seqno, pcb->rcv_nxt, pcb->rcv_nxt + pcb->rcv_wnd-1)){
      tcp_ack_now(pcb);
    }
  }
}

/**
 * Parses the options contained in the incoming segment. 
 *
 * Called from tcp_listen_input() and tcp_process().
 * Currently, only the MSS option is supported!
 *
 * @param pcb the tcp_pcb for which a segment arrived
 */
static void
tcp_parseopt(struct tcp_pcb *pcb)
{
  u16_t c, max_c;
  u16_t mss;
  u8_t *opts, opt;
#if LWIP_TCP_TIMESTAMPS
  u32_t tsval;
#endif

  opts = (u8_t *)tcphdr + TCP_HLEN;

  /* Parse the TCP MSS option, if present. */
  if(TCPH_HDRLEN(tcphdr) > 0x5) {
    max_c = (TCPH_HDRLEN(tcphdr) - 5) << 2;
    for (c = 0; c < max_c; ) {
      opt = opts[c];
      switch (opt) {
      case 0x00:
        /* End of options. */
        LWIP_DEBUGF(TCP_INPUT_DEBUG, ("tcp_parseopt: EOL\n"));
        return;
      case 0x01:
        /* NOP option. */
        ++c;
        LWIP_DEBUGF(TCP_INPUT_DEBUG, ("tcp_parseopt: NOP\n"));
        break;
      case 0x02:
        LWIP_DEBUGF(TCP_INPUT_DEBUG, ("tcp_parseopt: MSS\n"));
        if (opts[c + 1] != 0x04 || c + 0x04 > max_c) {
          /* Bad length */
          LWIP_DEBUGF(TCP_INPUT_DEBUG, ("tcp_parseopt: bad length\n"));
          return;
        }
        /* An MSS option with the right option length. */
        mss = (opts[c + 2] << 8) | opts[c + 3];
        /* Limit the mss to the configured TCP_MSS and prevent division by zero */
        pcb->mss = ((mss > TCP_MSS) || (mss == 0)) ? TCP_MSS : mss;
        /* Advance to next option */
        c += 0x04;
        break;
#if LWIP_TCP_TIMESTAMPS
      case 0x08:
        LWIP_DEBUGF(TCP_INPUT_DEBUG, ("tcp_parseopt: TS\n"));
        if (opts[c + 1] != 0x0A || c + 0x0A > max_c) {
          /* Bad length */
          LWIP_DEBUGF(TCP_INPUT_DEBUG, ("tcp_parseopt: bad length\n"));
          return;
        }
        /* TCP timestamp option with valid length */
        tsval = (opts[c+2]) | (opts[c+3] << 8) | 
          (opts[c+4] << 16) | (opts[c+5] << 24);
        if (flags & TCP_SYN) {
          pcb->ts_recent = ntohl(tsval);
          pcb->flags |= TF_TIMESTAMP;
        } else if (TCP_SEQ_BETWEEN(pcb->ts_lastacksent, seqno, seqno+tcplen)) {
          pcb->ts_recent = ntohl(tsval);
        }
        /* Advance to next option */
        c += 0x0A;
        break;
#endif
      default:
        LWIP_DEBUGF(TCP_INPUT_DEBUG, ("tcp_parseopt: other\n"));
        if (opts[c + 1] == 0) {
          LWIP_DEBUGF(TCP_INPUT_DEBUG, ("tcp_parseopt: bad length\n"));
          /* If the length field is zero, the options are malformed
             and we don't process them further. */
          return;
        }
        /* All other options have a length field, so that we easily
           can skip past them. */
        c += opts[c + 1];
      }
    }
  }
}

#endif /* LWIP_TCP */
