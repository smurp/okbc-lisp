/*  gcc -c -o connect.o connect.c  */

/* This file is part of the 
 *
 *	Delta Project  (ConversationBuilder)  
 *	Human-Computer Interaction Laboratory
 *	University of Illinois at Urbana-Champaign
 *	Department of Computer Science
 *	1304 W. Springfield Avenue
 *	Urbana, Illinois 61801
 *	USA
 *
 *	c 1989,1990,1991,1992 Board of Trustees
 *		University of Illinois
 *		All Rights Reserved
 *
 * This code is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY. No author or distributor accepts
 * responsibility to anyone for the consequences of using this code
 * or for whether it serves any particular purpose or works at all,
 * unless explicitly stated in a written agreement.
 *
 * Everyone is granted permission to copy, modify and redistribute
 * this code, except that the original author(s) must be given due credit,
 * and this copyright notice must be preserved on all copies.
 *
 *	Author:  Alan Carroll (carroll@cs.uiuc.edu)
 *
 *	Project Leader:  Simon Kaplan (kaplan@cs.uiuc.edu)
 *	Direct enquiries to the project leader please.
 */

/*
 * Twiddled by Doug Bogia on 02/13/92. 
 * An option to ignore interrupt (SIGINT) was added so the interrupt
 * to the common lisp process wouldn't kill the underlying connect.
 */

/* Provide a direct tty connection to the message bus */
/* $Source: /import/kaplan/kaplan/carroll/cb/mbus/commands/RCS/connect.c,v $ */

static char rcsid[] = "$Revision: 2.1.1.2 $ $Date: 91/11/15 13:37:56 $ $State: Exp $ $Author: carroll $";

/* ------------------------------------------------------------------------- */
#include "connect.h"

#include <netdb.h>
#include <sys/signal.h>

/* ------------------------------------------------------------------------- */
static int trace_fd = -1;
static char *host = NULL;
static int noint = 0;

/* ------------------------------------------------------------------------- */
void
bomb(s) char *s;
{
  perror(s);
  exit(1);
}
/* ------------------------------------------------------------------------- */
int
ConnectSocket(host,port)
     char *host;
     int port;
{
  int sock;
  int flags;
  struct sockaddr_in saddr;
  struct hostent *h;
  char hostname[64];

  if (port <= 0) port = 0x956;		/* magic number! */
  if (NULL == host || 0 == *host)
    {
      host = hostname;
      if (0 > gethostname(host,64)) 
	 /*   bomb("Can't get host name"); */
	perror("Can't get host name");
        return -1;
    }

  sock = socket(AF_INET, SOCK_STREAM, IPPROTO_TCP);
  if (sock < 0) 
    /*  bomb("Cannot open socket");  */
    { perror("Cannot open socket");
      return -1;
    }
  h = gethostbyname(host);

  if (NULL == h) 
    /*    bomb("Cannot find host");   */
    { perror("Cannot find host");
      close(sock);
      return -1;
    }
  if (h->h_addr_list == 0) 
    /*    bomb("No addresses for host"); */
    { perror("No addresses for host");
      close(sock);
      return -1;
    }

  saddr.sin_family = AF_INET;
  saddr.sin_addr.s_addr = INADDR_ANY;
  saddr.sin_port = 0;			/* anywhere */

  saddr.sin_family = AF_INET;
  memcpy((char *) &saddr.sin_addr, h->h_addr_list[0], h->h_length);
  saddr.sin_port = htons(port);

  if (connect(sock, (struct sockaddr *) &saddr, sizeof(saddr)))
    /* ----bomb("Couldn't connect to Mbus");    */
    {
      close(sock);
      return -1;
    }
  return sock;
}
