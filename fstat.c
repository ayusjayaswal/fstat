/*-
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * Copyright (c) 2009 Stanislav Sedov <stas@FreeBSD.org>
 * Copyright (c) 1988, 1993
 *	The Regents of the University of California.  All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 3. Neither the name of the University nor the names of its contributors
 *    may be used to endorse or promote products derived from this software
 *    without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE REGENTS AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE REGENTS OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 */

#include <sys/param.h>
#include <sys/user.h>
#include <sys/stat.h>
#include <sys/socket.h>
#include <sys/socketvar.h>
#include <sys/sysctl.h>
#include <sys/queue.h>
#include <sys/un.h>

#include <netinet/in.h>

#include <arpa/inet.h>

#include <assert.h>
#include <ctype.h>
#include <err.h> // # remove this later
#include <libprocstat.h>
#include <limits.h>
#include <pwd.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <stddef.h>
#include <string.h>
#include <unistd.h>
#include <netdb.h>

#include <libxo/xo.h>

#include "functions.h"

static int 	fsflg,	/* show files on same filesystem as file(s) argument */
		pflg,	/* show files open by a particular pid */
		sflg,	/* show socket details */
		uflg;	/* show files open by a particular (effective) user */
static int 	checkfile; /* restrict to particular files or filesystems */
static int	nflg;	/* (numerical) display f.s. and rdev as dev_t */
static int	mflg;	/* include memory-mapped files */
static int	vflg;	/* be verbose */

typedef struct devs {
	struct devs	*next;
	uint64_t	fsid;
	uint64_t	ino;
	const char	*name;
} DEVS;

static DEVS *devs;
static char *memf, *nlistf;

static int	getfname(const char *filename);
static void	dofiles(struct procstat *procstat, struct kinfo_proc *p);
static void	print_access_flags(int flags);
static void	print_file_info(struct procstat *procstat,
    struct filestat *fst, const char *uname, const char *cmd, int pid);
static void	print_pipe_info(struct procstat *procstat,
    struct filestat *fst);
static void	print_pts_info(struct procstat *procstat,
    struct filestat *fst);
static void	print_sem_info(struct procstat *procstat,
    struct filestat *fst);
static void	print_shm_info(struct procstat *procstat,
    struct filestat *fst);
static void	print_socket_info(struct procstat *procstat,
    struct filestat *fst);
static void	print_vnode_info(struct procstat *procstat,
    struct filestat *fst);
static void	usage(void) __dead2;

int
do_fstat(int argc, char **argv)
{
	struct kinfo_proc *p;
	struct passwd *passwd;
	struct procstat *procstat;
	int arg, ch, what;
	int cnt, i;
	arg = 0;
	what = KERN_PROC_PROC;
	nlistf = memf = NULL;
  /* parse --libxo arguments first */
  argc = xo_parse_args(argc, argv);
  if (argc < 0)
    xo_errx(1, "libxo argument parsing failed");

	while ((ch = getopt(argc, argv, "fmnp:su:vN:M:")) != -1)
		switch((char)ch) {
		case 'f':
			fsflg = 1;
			break;
		case 'M':
			memf = optarg;
			break;
		case 'N':
			nlistf = optarg;
			break;
		case 'm':
			mflg = 1;
			break;
		case 'n':
			nflg = 1;
			break;
		case 'p':
			if (pflg++)
				usage();
			if (!isdigit(*optarg)) {
				xo_warnx("-p requires a process id");
				usage();
			}
			what = KERN_PROC_PID;
			arg = atoi(optarg);
			break;
		case 's':
			sflg = 1;
			break;
		case 'u':
			if (uflg++)
				usage();
			if (!(passwd = getpwnam(optarg)))
				xo_errx(1, "%s: unknown uid", optarg);
			what = KERN_PROC_UID;
			arg = passwd->pw_uid;
			break;
		case 'v':
			vflg = 1;
			break;
		case '?':
		default:
			usage();
		}

	if (*(argv += optind)) {
		for (; *argv; ++argv) {
			if (getfname(*argv))
				checkfile = 1;
		}
		if (!checkfile)	/* file(s) specified, but none accessible */
			exit(1);
	}

	if (fsflg && !checkfile) {
		/* -f with no files means use wd */
		if (getfname(".") == 0)
			exit(1);
		checkfile = 1;
	}

//	if (memf != NULL)
//		procstat = procstat_open_kvm(nlistf, memf);
//	else
//		procstat = procstat_open_sysctl();
//	if (procstat == NULL)
//		errx(1, "procstat_open()");
//	p = procstat_getprocs(procstat, what, arg, &cnt);
//	if (p == NULL)
//		errx(1, "procstat_getprocs()");
//		LESS CONFIDENCE ON FOLLOWING LINES

  if (memf != NULL)
		procstat = procstat_open_kvm(nlistf, memf);
	else
		procstat = procstat_open_sysctl();
	if (procstat == NULL)
		xo_errx(1, "procstat_open_sysctl() failed: %s", xo_strerror(errno));
	p = procstat_getprocs(procstat, what, arg, &cnt);
	if (p == NULL)
		xo_errx(1, "procstat_getprocs() failed: %s", xo_strerror(errno));

  xo_open_list("fstat-entry");
	/*
	 * Print header.
	 */
xo_emit_h("{T:USER/%-8s}{T:/%-10s}{T:PID/%5s}{T:FD/%4s}", "USER", "CMD", "PID",
        "FD");
	if (nflg)
		xo_emit_h("{T:DEVICE/%-6s}{T:INODE/%10s}{T:MODE/%12s}{T:SIZE_OR_DEV/%-6s}
            {T:ACCESS/%3s}", "DEV", "INUM", "MODE", "SZ|DV", "R/W");
	else
		xo_emit_h("{T:MOUNT/%-10s}{T:INODE/%10s}{T:MODE/%12s}{T:SIZE_OR_DEV/%-6s}
            {T:ACCESS/%3s}", "MOUNT", "INUM", "MODE", "SZ|DV", "R/W");

	if (checkfile && fsflg == 0)
		xo_emit_h("{T:NAME/ %s}", " NAME");
	xo_emit_h("\n");

	/*
	 * Go through the process list.
	 */
	for (i = 0; i < cnt; i++) {
		if (p[i].ki_stat == SZOMB)
			continue;
		dofiles(procstat, &p[i]);
	}
  xo_close_list("fstat-entry");
	procstat_freeprocs(procstat, p);
	procstat_close(procstat);
  xo_finish();
	return (0);
}

static void
dofiles(struct procstat *procstat, struct kinfo_proc *kp)
{
	const char *cmd;
	const char *uname;
	struct filestat *fst;
	struct filestat_list *head;
	int pid;

	uname = user_from_uid(kp->ki_uid, 0);
	pid = kp->ki_pid;
	cmd = kp->ki_comm;

	head = procstat_getfiles(procstat, kp, mflg);
	if (head == NULL)
		return;
	STAILQ_FOREACH(fst, head, next)
		print_file_info(procstat, fst, uname, cmd, pid);
	procstat_freefiles(procstat, head);
}


static void
print_file_info(struct procstat *procstat, struct filestat *fst,
    const char *uname, const char *cmd, int pid)
{
	struct vnstat vn;
	DEVS *d;
	const char *filename;
	int error, fsmatch = 0;
	char errbuf[_POSIX2_LINE_MAX];

	filename = NULL;
	if (checkfile != 0) {
		if (fst->fs_type != PS_FST_TYPE_VNODE &&
		    fst->fs_type != PS_FST_TYPE_FIFO)
			return;
		error = procstat_get_vnode_info(procstat, fst, &vn, errbuf);
		if (error != 0)
			return;

		for (d = devs; d != NULL; d = d->next)
			if (d->fsid == vn.vn_fsid) {
				fsmatch = 1;
				if (d->ino == vn.vn_fileid) {
					filename = d->name;
					break;
				}
			}
		if (fsmatch == 0 || (filename == NULL && fsflg == 0))
			return;
	}
  xo_open_instance("file-details");
	/*
	 * Print entry prefix.
	 */
  xo_emit("{k:user/%-8.8s} {k:command/%-10s} {k:pid/%5d}", uname, cmd, pid);
//	if (fst->fs_uflags & PS_FST_UFLAG_TEXT)
//		printf(" text");
//	else if (fst->fs_uflags & PS_FST_UFLAG_CDIR)
//		printf("   wd");
//	else if (fst->fs_uflags & PS_FST_UFLAG_RDIR)
//		printf(" root");
//	else if (fst->fs_uflags & PS_FST_UFLAG_TRACE)
//		printf("   tr");
//	else if (fst->fs_uflags & PS_FST_UFLAG_MMAP)
//		printf(" mmap");
//	else if (fst->fs_uflags & PS_FST_UFLAG_JAIL)
//		printf(" jail");
//	else if (fst->fs_uflags & PS_FST_UFLAG_CTTY)
//		printf(" ctty");
//	else
//		printf(" %4d", fst->fs_fd);
  if (fst->fs_uflags & PS_FST_UFLAG_TEXT)
		xo_emit(" {:fd_description/text%4s}", "");
	else if (fst->fs_uflags & PS_FST_UFLAG_CDIR)
		xo_emit(" {:fd_description/%6s}", "wd");
	else if (fst->fs_uflags & PS_FST_UFLAG_RDIR)
		xo_emit(" {:fd_description/%6s}", "root");
	else if (fst->fs_uflags & PS_FST_UFLAG_TRACE)
		xo_emit(" {:fd_description/%6s}", "tr");
	else if (fst->fs_uflags & PS_FST_UFLAG_MMAP)
		xo_emit(" {:fd_description/%6s}", "mmap");
	else if (fst->fs_uflags & PS_FST_UFLAG_JAIL)
		xo_emit(" {:fd_description/%6s}", "jail");
	else if (fst->fs_uflags & PS_FST_UFLAG_CTTY)
		xo_emit(" {:fd_description/%6s}", "ctty");
	else
		xo_emit(" {:fd_number/%4d}", fst->fs_fd);

	/*
	 * Print type-specific data.
	 */
switch (fst->fs_type) {
	case PS_FST_TYPE_FIFO:
		xo_emit("{e:file_type/fifo}");
		print_vnode_info(procstat, fst);
		break;
	case PS_FST_TYPE_VNODE:
		xo_emit("{e:file_type/vnode}");
		print_vnode_info(procstat, fst);
		break;
	case PS_FST_TYPE_SOCKET:
		xo_emit("{e:file_type/socket}");
		print_socket_info(procstat, fst);
		break;
	case PS_FST_TYPE_PIPE:
		xo_emit("{e:file_type/pipe}");
		print_pipe_info(procstat, fst);
		break;
	case PS_FST_TYPE_PTS:
		xo_emit("{e:file_type/pts}");
		print_pts_info(procstat, fst);
		break;
	case PS_FST_TYPE_SHM:
		xo_emit("{e:file_type/shm}");
		print_shm_info(procstat, fst);
		break;
	case PS_FST_TYPE_SEM:
		xo_emit("{e:file_type/sem}");
		print_sem_info(procstat, fst);
		break;
	case PS_FST_TYPE_DEV:
        xo_emit("{e:file_type/dev}");
		xo_emit(" {:device_details/n\\/a%*s}", 28, "");
		print_access_flags(fst->fs_fflags);
		break;
	default:	
		xo_emit("{e:file_type/unknown}");
		if (vflg)
			xo_warnx("unknown file type %d for file %d of pid %d",
			    fst->fs_type, fst->fs_fd, pid);
		xo_emit(" {:unknown_type_details/n\\/a%*s}", 28, "");
		print_access_flags(fst->fs_fflags);
	}

	if (filename && !fsflg)
    xo_emit(" {:name_from_argument/ %s}", filename);

	xo_close_instance("file-details");
	xo_emit("\n");
}

static char *
addr_to_string(struct sockaddr_storage *ss, char *buffer, int buflen)
{
	char buffer2[INET6_ADDRSTRLEN];
	struct sockaddr_in6 *sin6;
	struct sockaddr_in *sin;
	struct sockaddr_un *sun;

	switch (ss->ss_family) {
	case AF_LOCAL:
		sun = (struct sockaddr_un *)ss;
		if (strlen(sun->sun_path) == 0)
			strlcpy(buffer, "-", buflen);
		else
			strlcpy(buffer, sun->sun_path, buflen);
		break;

	case AF_INET:
		sin = (struct sockaddr_in *)ss;
		if (sin->sin_addr.s_addr == INADDR_ANY)
			snprintf(buffer, buflen, "%s:%d", "*",
			    ntohs(sin->sin_port));
		else if (inet_ntop(AF_INET, &sin->sin_addr, buffer2,
		    sizeof(buffer2)) != NULL)
			snprintf(buffer, buflen, "%s:%d", buffer2,
		            ntohs(sin->sin_port));
		break;

	case AF_INET6:
		sin6 = (struct sockaddr_in6 *)ss;
		if (IN6_IS_ADDR_UNSPECIFIED(&sin6->sin6_addr))
			snprintf(buffer, buflen, "%s.%d", "*",
			    ntohs(sin6->sin6_port));
		else if (inet_ntop(AF_INET6, &sin6->sin6_addr, buffer2,
		    sizeof(buffer2)) != NULL)
			snprintf(buffer, buflen, "%s.%d", buffer2,
			    ntohs(sin6->sin6_port));
		else
			strlcpy(buffer, "-", buflen);
		break;

	default:
		strlcpy(buffer, "", buflen);
		break;
	}
	return buffer;
}


static void
print_socket_info(struct procstat *procstat, struct filestat *fst)
{
	static const char *stypename[] = {
		"unused",	/* 0 */
		"stream",	/* 1 */
		"dgram",	/* 2 */
		"raw",		/* 3 */
		"rdm",		/* 4 */
		"seqpak"	/* 5 */
	};
#define STYPEMAX 5
	struct sockstat sock;
	struct protoent *pe;
	char errbuf[_POSIX2_LINE_MAX];
	char src_addr[PATH_MAX], dst_addr[PATH_MAX];
	struct sockaddr_un *sun;
	int error;
	static int isopen;

	xo_open_container("socket");
	error = procstat_get_socket_info(procstat, fst, &sock, errbuf);
  if (error != 0) {
      xo_emit(" {:socket_error/error}");
      xo_close_container("socket");
      return;
  }
  if (sock.type > STYPEMAX)
		xo_emit("*{:socket_domain/%s} {:socket_type_unknown/?%d}", sock.dname, 
            sock.type);
	else
		xo_emit("*{:socket_domain/%s} {:socket_type/%s}", sock.dname, 
            stypename[sock.type]);

	/*
	 * protocol specific formatting
	 *
	 * Try to find interesting things to print.  For internet and unix
	 * sockets, its the address of the socket pcb.  For unix it is also the
	 * address of the connected pcb (if connected).  Otherwise just print
	 * the protocol number and address of the socket itself.
	 * The idea is not to duplicate netstat, but to make available enough
	 * information for further analysis.
	 */
	switch (sock.dom_family) {
	case AF_INET:
	case AF_INET6:
		if (!isopen)
			setprotoent(++isopen);
		if ((pe = getprotobynumber(sock.proto)) != NULL)
      xo_emit(" {:protocol_name/%s}", pe->p_name);
		else
      xo_emit(" {:protocol_number/%d}", sock.proto);
		if (sock.so_pcb != 0)
      xo_emit(" {:pcb_address/%lx}", (u_long)sock.so_pcb);
		if (!sflg)
			break;
    xo_emit(" {:local-address/%s} <-> {:remote-address/%s}",
        addr_to_string(&sock.sa_local, src_addr, sizeof(src_addr)),
        addr_to_string(&sock.sa_peer, dst_addr, sizeof(dst_addr)));
		break;
	case AF_UNIX:
		/* print address of pcb and connected pcb */
		if (sock.so_pcb != 0) {
      xo_emit(" {:pcb_address/%lx}", (u_long)sock.so_pcb);
			if (sock.unp_conn) {
				char shoconn[4], *cp;

				cp = shoconn;
				if (!(sock.so_rcv_sb_state & SBS_CANTRCVMORE))
					*cp++ = '<';
				*cp++ = '-';
				if (!(sock.so_snd_sb_state & SBS_CANTSENDMORE))
					*cp++ = '>';
				*cp = '\0';
				xo_emit(" {:connection_status/%s} {:connected_pcb_address/%lx}",
                shoconn, (u_long)sock.unp_conn);
			}
		}
		if (!sflg)
			break;
		sun = (struct sockaddr_un *)&sock.sa_local;
		/*
		 * While generally we like to print two addresses,
		 * local and peer, for sockets, it turns out to be
		 * more useful to print the first non-null address for
		 * local sockets, as typically they aren't bound and
		 *  connected, and the path strings can get long.
		 */
		if (sun->sun_path[0] != 0)
			addr_to_string(&sock.sa_local,
			    src_addr, sizeof(src_addr));
		else
			addr_to_string(&sock.sa_peer,
			    src_addr, sizeof(src_addr));
		xo_emit(" {:unix_socket_path/ %s}", src_addr);
		break;
	default:
		/* print protocol number and socket address */
    xo_emit(" {:protocol_number/%d} {:socket_address/%lx}", sock.proto, 
            (u_long)sock.so_addr);
	}
  xo_close_container("socket");
}

static void
print_pipe_info(struct procstat *procstat, struct filestat *fst)
{
	struct pipestat ps;
	char errbuf[_POSIX2_LINE_MAX];
	int error;

  xo_open_container("pipe");

	error = procstat_get_pipe_info(procstat, fst, &ps, errbuf);
  if (error != 0) {
    xo_emit(" {:pipe-error/error}");
    xo_close_container("pipe");
    return;
  }
	xo_emit(" {:pipe-addr/%#lx} <-> {:peer-addr/%#lx}",
	    (u_long)ps.addr, (u_long)ps.peer);
	xo_emit(" {:buffer-count/%6zd}", ps.buffer_cnt);
	print_access_flags(fst->fs_fflags);
  xo_close_container("pipe");
}


static void
print_pts_info(struct procstat *procstat, struct filestat *fst)
{
	struct ptsstat pts;
	char errbuf[_POSIX2_LINE_MAX];
	int error;

  xo_open_container("pts");
	error = procstat_get_pts_info(procstat, fst, &pts, errbuf);
	if (error != 0) {
    xo_emit(" {:pts_error/error}");
    xo_close_container("pts");
		return;
	}
	xo_emit("*{:pts_indicator/pseudo-terminal master} ");
	if (nflg || !*pts.devname) {
		xo_emit("{:device_number/%#10jx}", (uintmax_t)pts.dev);
	} else {
		xo_emit("{:device_name/%10s}", pts.devname);
	}
	print_access_flags(fst->fs_fflags);
  xo_close_container("pts");
}

static void
print_sem_info(struct procstat *procstat, struct filestat *fst)
{
	struct semstat sem;
	char errbuf[_POSIX2_LINE_MAX];
	char mode[15];
	int error;

	error = procstat_get_sem_info(procstat, fst, &sem, errbuf);
	if (error != 0) {
		xo_emit(" {:sem_error/error}");
		return;
	}
	xo_open_container("semaphore");
	if (nflg) {
		xo_emit(" {:path/%15s}", "");
		(void)snprintf(mode, sizeof(mode), "%o", sem.mode);
	} else {
		xo_emit(" {:path/%-15s}", fst->fs_path != NULL ? fst->fs_path : "-");
		strmode(sem.mode, mode);
	}
	xo_emit(" {:mode/%10s} {:value/%6u}", mode, sem.value);
	print_access_flags(fst->fs_fflags);
	xo_close_container("semaphore");
}

static void
print_shm_info(struct procstat *procstat, struct filestat *fst)
{
	struct shmstat shm;
	char errbuf[_POSIX2_LINE_MAX];
	char mode[15];
	int error;

	error = procstat_get_shm_info(procstat, fst, &shm, errbuf);
	if (error != 0) {
		xo_emit(" {:shm_error/error}");
		return;
	}

	xo_open_container("shared_memory");
	if (nflg) {
		xo_emit(" {:path/%15s}", "");
		(void)snprintf(mode, sizeof(mode), "%o", shm.mode);
	} else {
		xo_emit(" {:path/%-15s}", fst->fs_path != NULL ? fst->fs_path : "-");
		strmode(shm.mode, mode);
	}
	xo_emit(" {:mode/%10s} {:size/%6ju}", mode, shm.size);
	print_access_flags(fst->fs_fflags);
	xo_close_container("shared_memory");
}

static void
print_vnode_info(struct procstat *procstat, struct filestat *fst)
{
	struct vnstat vn;
	char errbuf[_POSIX2_LINE_MAX];
	char mode[15];
	const char *badtype;
	int error;

	badtype = NULL;
	error = procstat_get_vnode_info(procstat, fst, &vn, errbuf);
	if (error != 0)
		badtype = errbuf;
	else if (vn.vn_type == PS_FST_VTYPE_VBAD)
		badtype = "bad";
	else if (vn.vn_type == PS_FST_VTYPE_VNON)
		badtype = "none";

	xo_open_container("vnode");

	if (badtype != NULL) {
		xo_emit(" {:fsid/-} {:mount_dir/-} {:fileid/-} {:mode/%10s} {:size_or_dev/-}",
            badtype);
		xo_close_container("vnode");
		return;
	}

	if (nflg)
		xo_emit(" {:fsid/%#5jx}", (uintmax_t)vn.vn_fsid);
	else if (vn.vn_mntdir != NULL)
		xo_emit(" {:mount_dir/%-8s}", vn.vn_mntdir);
	else
		xo_emit(" {:mount_dir/-}");

	/*
	 * Print access mode.
	 */
	if (nflg)
		(void)snprintf(mode, sizeof(mode), "%o", vn.vn_mode);
	else
		strmode(vn.vn_mode, mode);

	xo_emit(" {:fileid/%6jd} {:mode/%10s}", (intmax_t)vn.vn_fileid, mode);

	if (vn.vn_type == PS_FST_VTYPE_VBLK || vn.vn_type == PS_FST_VTYPE_VCHR) {
		if (nflg || !*vn.vn_devname)
			xo_emit(" {:device/%#6jx}", (uintmax_t)vn.vn_dev);
		else
			xo_emit(" {:device/%6s}", vn.vn_devname);
	} else {
		xo_emit(" {:size/%6ju}", (uintmax_t)vn.vn_size);
	}

	print_access_flags(fst->fs_fflags);
	xo_close_container("vnode");
}


static void
print_access_flags(int flags)
{
	char rw[3];
  xo_open_container("access");
	rw[0] = '\0';
	if (flags & PS_FST_FFLAG_READ)
		strcat(rw, "r");
	if (flags & PS_FST_FFLAG_WRITE)
		strcat(rw, "w");
  xo_emit(" {:access_flags/%2s}", rw);
  xo_close_container("access");
}

int
getfname(const char *filename)
{
	struct stat statbuf;
	DEVS *cur;
	
	if (stat(filename, &statbuf)) {
		xo_warn("%s", filename);
		return (0);
	}
	if ((cur = malloc(sizeof(DEVS))) == NULL)
		xo_err(1, NULL);
	
	cur->next = devs;
	devs = cur;
	cur->ino = statbuf.st_ino;
	cur->fsid = statbuf.st_dev;
	cur->name = filename;
	return (1);
}

static void
usage(void)
{
	xo_error("usage: fstat [-fmnv] [-M core] [-N system] [-p pid] [-u user] 
          [file ...]\n");
	exit(1);
}
