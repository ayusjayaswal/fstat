PROG=	fstat
SRCS=	fstat.c fuser.c main.c
LINKS=	${BINDIR}/fstat ${BINDIR}/fuser
LIBADD=	procstat xo

MAN1=	fuser.1 fstat.1

.include <bsd.prog.mk>
