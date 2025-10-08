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

/* Standard header files that bus programs want to include */
/* $Source: /import/kaplan/kaplan/carroll/cb/mbus/commands/RCS/header.h,v $ */

/* $Revision: 2.1.1.2 $
 * $Date: 91/11/15 13:37:52 $
 * $State: Exp $
 * $Author: carroll $
 */

/* ------------------------------------------------------------------------- */

#include <stdio.h>
#ifdef NeXT
#include <string.h>
#include <sys/fcntl.h>
#else
#include <fcntl.h>
#endif
#include <sys/types.h>
#include <sys/socket.h>
#include <netinet/in.h>

#include <sys/errno.h>

