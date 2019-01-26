/* See LICENSE file for license details. */
#include <sys/select.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/un.h>

#include <ctype.h>
#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <netdb.h>
#include <netinet/in.h>
#include <pwd.h>
#include <signal.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

#define READ_FD 6
#define WRITE_FD 7

char *argv0;

#include "arg.h"

#ifdef NEED_STRLCPY
size_t strlcpy(char *, const char *, size_t);
#endif /* NEED_STRLCPY */

#define IRC_CHANNEL_MAX   200
#define IRC_NICK_MAX      200
#define IRC_MSG_MAX       512 /* quaranteed to be <= than PIPE_BUF */
#define PING_TIMEOUT      300
#define UMODE_MAX          10
#define CMODE_MAX          50

enum { TOK_NICKSRV = 0, TOK_USER, TOK_CMD, TOK_CHAN, TOK_ARG, TOK_TEXT, TOK_LAST };

typedef struct Nick Nick;
struct Nick {
        char name[IRC_NICK_MAX];
        char prefix;
	Nick *next;
};

typedef struct Channel Channel;
struct Channel {
	int fdin;
	char name[IRC_CHANNEL_MAX]; /* channel name (normalized) */
	char inpath[PATH_MAX];      /* input path */
        char outpath[PATH_MAX];     /* output path */
        Nick *nicks;
	Channel *next;
};

static void      cap_parse(char *);
static Channel * channel_add(const char *);
static Channel * channel_find(const char *);
static Channel * channel_join(const char *);
static void      channel_leave(Channel *);
static Channel * channel_new(const char *);
static void      channel_normalize_name(char *);
static void      channel_normalize_path(char *);
static int       channel_open(Channel *);
static void      channel_print(Channel *, const char *);
static int       channel_reopen(Channel *);
static void      channel_rm(Channel *);
static void      create_dirtree(const char *);
static void      create_filepath(char *, size_t, const char *, const char *, const char *);
static void      ewritestr(int, const char *);
static void      handle_channels_input(int, Channel *);
static void      handle_server_output(int, int);
static void      loginkey(int, const char *);
static void      loginuser(int, const char *, const char *, const char *);
#define name_add(c, n) name_add3((c), (n), '\0')
static void      name_add3(const char *, const char *, const char);
static Nick *    name_find(Channel *, const char *);
static void      name_menick(const char *, const char *);
static void      name_mode(const char *, char *, char *);
static void      name_nick(const char *, const char *);
static void      name_quit(const char *, const char *, const char *);
static int       name_rm(const char *, const char *);
static int       name_rm3(Channel *, const char *, char *);
static void      parse_cmodes(char *);
static void      parse_prefix(char *);
static void      proc_channels_input(int, Channel *, char *);
static void      proc_channels_privmsg(int, Channel *, char *);
static void      proc_names(const char *, char *);
static void      proc_server_cmd(int, char *);
static int       ptr_split(const char *, const char *, const char *, const char *);
static int       read_line(int, char *, size_t);
static void      run(int, int, const char *);
static void      setup(void);
static void      sighandler(int);
static int       tcpopen(const char *, const char *);
static void      tokenize(char **, char *);
static int       udsopen(const char *);
static void      usage(void);

static int      isrunning = 1;
static time_t   last_response = 0;
static Channel *channels = NULL;
static Channel *channelmaster = NULL;
static char     nick[32];          /* active nickname at runtime */
static char     _nick[32];         /* nickname at startup */
static char     ircpath[PATH_MAX]; /* irc dir (-i) */
static char     msg[IRC_MSG_MAX];  /* message buf used for communication */
static int      trackprefix = 1;   /* flag to track user prefixes */
static char     upref[UMODE_MAX];  /* user prefixes in use on this server */
static char     umodes[UMODE_MAX]; /* modes corresponding to the prefixes */
static char     cmodes[CMODE_MAX]; /* channel modes in use on this server */


static void
usage(void)
{
        fprintf(stderr, "usage: %s <-s host> [-t] [-P] [-i <irc dir>] "
                "[-p <port>] [-U <sockname>] [-n <nick>] [-k <password>] "
                "[-u <username>] [-f <fullname>]\n",
                argv0);
	exit(1);
}

static void
ewritestr(int fd, const char *s)
{
	size_t len, off = 0;
	int w = -1;

	len = strlen(s);
	for (off = 0; off < len; off += w) {
		if ((w = write(fd, s + off, len - off)) == -1)
			break;
		off += w;
	}
	if (w == -1) {
		fprintf(stderr, "%s: write: %s\n", argv0, strerror(errno));
		exit(1);
	}
}

/* creates directories bottom-up, if necessary */
static void
create_dirtree(const char *dir)
{
	char tmp[PATH_MAX], *p;
	struct stat st;
	size_t len;

	strlcpy(tmp, dir, sizeof(tmp));
	len = strlen(tmp);
	if (len > 0 && tmp[len - 1] == '/')
		tmp[len - 1] = '\0';

	if ((stat(tmp, &st) != -1) && S_ISDIR(st.st_mode))
		return; /* dir exists */

	for (p = tmp + 1; *p; p++) {
		if (*p != '/')
			continue;
		*p = '\0';
		mkdir(tmp, S_IRWXU);
		*p = '/';
	}
	mkdir(tmp, S_IRWXU);
}

static void
channel_normalize_path(char *s)
{
	for (; *s; s++) {
		if (isalpha(*s))
			*s = tolower(*s);
		else if (!isdigit(*s) && !strchr(".#&+!-", *s))
			*s = '_';
	}
}

static void
channel_normalize_name(char *s)
{
	char *p;

	/* advance over the channel prefix char (&#) and any possible prefix
	 * characters if we have received a message for opers
	 * (e.g. NOTICE @#chan :hey ops) */
        while (*s == '&' || *s == '#' || strchr(upref, s[0]) != NULL)
		s++;
	for (p = s; *s; s++) {
		/* sanitise the channel name of invalid chars and downcase
		 * alphanumerics */
		if (!strchr(" ,&#\x07", *s)) {
			*p = isalpha(*s) ? tolower(*s) : *s;
			p++;
		}
	}
	*p = '\0';
}

static void
create_filepath(char *filepath, size_t len, const char *path,
	const char *channel, const char *suffix)
{
	int r;

	if (channel[0]) {
		r = snprintf(filepath, len, "%s/%s", path, channel);
		if (r < 0 || (size_t)r >= len)
			goto error;
		create_dirtree(filepath);
		r = snprintf(filepath, len, "%s/%s/%s", path, channel, suffix);
		if (r < 0 || (size_t)r >= len)
			goto error;
	} else {
		r = snprintf(filepath, len, "%s/%s", path, suffix);
		if (r < 0 || (size_t)r >= len)
			goto error;
	}
	return;

error:
	fprintf(stderr, "%s: path to irc directory too long\n", argv0);
	exit(1);
}

static int
channel_open(Channel *c)
{
	int fd;
	struct stat st;

	/* make "in" fifo if it doesn't exist already. */
	if (lstat(c->inpath, &st) != -1) {
		if (!(st.st_mode & S_IFIFO))
			return -1;
	} else if (mkfifo(c->inpath, S_IRWXU)) {
		return -1;
	}
	c->fdin = -1;
	fd = open(c->inpath, O_RDONLY | O_NONBLOCK, 0);
	if (fd == -1)
		return -1;
	c->fdin = fd;

	return 0;
}

static int
channel_reopen(Channel *c)
{
	if (c->fdin > 2) {
		close(c->fdin);
		c->fdin = -1;
	}
	return channel_open(c);
}

static Channel *
channel_new(const char *name)
{
	Channel *c;
	char channelpath[PATH_MAX];

	strlcpy(channelpath, name, sizeof(channelpath));
	channel_normalize_path(channelpath);

	if (!(c = calloc(1, sizeof(Channel)))) {
		fprintf(stderr, "%s: calloc: %s\n", argv0, strerror(errno));
		exit(1);
	}
	c->next = NULL;
	strlcpy(c->name, name, sizeof(c->name));
	channel_normalize_name(c->name);

	create_filepath(c->inpath, sizeof(c->inpath), ircpath,
	                channelpath, "in");
	create_filepath(c->outpath, sizeof(c->outpath), ircpath,
	                channelpath, "out");
	return c;
}

static Channel *
channel_find(const char *name)
{
	Channel *c;
	char chan[IRC_CHANNEL_MAX];

	strlcpy(chan, name, sizeof(chan));
	channel_normalize_name(chan);
	for (c = channels; c; c = c->next) {
		if (!strcmp(chan, c->name))
			return c; /* already handled */
	}
	return NULL;
}

static Channel *
channel_add(const char *name)
{
	Channel *c;

	c = channel_new(name);
	if (channel_open(c) == -1) {
		fprintf(stderr, "%s: cannot create channel: %s: %s\n",
		         argv0, name, strerror(errno));
		free(c);
		return NULL;
	}
	if (!channels) {
		channels = c;
	} else {
		c->next = channels;
		channels = c;
        }
        c->nicks = NULL;
	return c;
}

static Channel *
channel_join(const char *name)
{
	Channel *c;

	if (!(c = channel_find(name)))
		c = channel_add(name);
	return c;
}

static void
channel_rm(Channel *c)
{
        Channel *p;
        Nick *n, *nn;

	if (channels == c) {
		channels = channels->next;
	} else {
		for (p = channels; p && p->next != c; p = p->next)
			;
		if (p && p->next == c)
			p->next = c->next;
        }

        for (n = c->nicks; n; n = nn) {
                nn = n->next;
                free(n);
        }

        free(c);
}

static void
channel_leave(Channel *c)
{
	if (c->fdin > 2) {
		close(c->fdin);
		c->fdin = -1;
	}
	/* remove "in" file on leaving the channel */
	unlink(c->inpath);
	channel_rm(c);
}

static void
loginkey(int ircfd, const char *key)
{
	snprintf(msg, sizeof(msg), "PASS %s\r\n", key);
	ewritestr(ircfd, msg);
}

static void
loginuser(int ircfd, const char *host, const char* username, const char *fullname)
{
	snprintf(msg, sizeof(msg), "NICK %s\r\nUSER %s localhost %s :%s\r\n",
	         nick, username, host, fullname);
	puts(msg);
	ewritestr(ircfd, msg);
}

static void
name_add3(const char *chan, const char *name, const char modes) {
        Channel *c;
        Nick *n;
        const char *p;

        if(!(c = channel_find(chan)))
                return;

        p = name;
        if (strchr(upref, p[0]) != NULL) {
                name++;
        }

        
        for(n = c->nicks; n; n = n->next) {
		if(!strcmp(name, n->name)) {
			/* name already exists in the channel, but twiddle prefix
			 * characters in case they've changed without us knowing.
			 * this also means that /NAMES can be used to reset nick
			 * state if we get confused. */
			if (trackprefix && p != name) {
				n->prefix = *p;
			}
			return;
		}
	}

        if (!(n = calloc(1, sizeof(Nick)))) {
		fprintf(stderr, "%s: calloc: %s\n", argv0, strerror(errno));
		exit(1);
	}

        if (trackprefix && p != name) {
                /* special people get prefix chars */
                n->prefix = *p;
        } else {
                n->prefix = modes;
        }
        
        strlcpy(n->name, name, sizeof(n->name));
	n->next = c->nicks;
	c->nicks = n;
}

static int
name_rm(const char *chan, const char *name) {
	Channel *c;
	Nick *n, *pn = NULL;

        if(!(c = channel_find(chan)))
                return 0;

        for(n = c->nicks; n; pn = n, n = n->next) {
		if(!strcmp(name, n->name)) {
                        if(pn)
                                pn->next = n->next;
                        else
                                c->nicks = n->next;
			free(n);
			return 1;
		}
	}
	return 0;
}

static int
name_rm3(Channel *c, const char *name, char *prefix) {
	Nick *n, *pn = NULL;

        for(n = c->nicks; n; pn = n, n = n->next) {
                if(!strcmp(name, n->name)) {
                        if(pn)
                                pn->next = n->next;
                        else
                                c->nicks = n->next;
                        if (prefix)
                                *prefix = n->prefix;
			free(n);
			return 1;
		}
	}
	return 0;
}

static void
name_quit(const char *name, const char *user, const char *text) {
	Channel *c;

        for(c = channels; c; c = c->next) {
		if(*c->name && name_rm3(c, name, NULL)) {
			snprintf(msg, sizeof(msg), "-!- %s(%s) has quit \"%s\"", name, user, text ? text : "");
			channel_print(c, msg);
		}
	}
}

static void
name_nick(const char *old, const char *new) {
        Channel *c;
        char tmp;

        for(c = channels; c; c = c->next) {
		if(*c->name && name_rm3(c, old, &tmp)) {
			name_add3(c->name, new, tmp);
			snprintf(msg, sizeof(msg), "-!- %s changed nick to \"%s\"", old, new);
			channel_print(c, msg);
		}
	}
}

static void
name_menick(const char* old, const char *new) {
        Channel *c;
        char tmp;

        snprintf(msg, sizeof(msg), "-!- changed nick to \"%s\"", new);

        for(c = channels; c; c = c->next) {
		if(*c->name && name_rm3(c, old, &tmp)) {
			name_add3(c->name, new, tmp);
		}
                channel_print(c, msg);
        }
}

static int
ptr_split(const char *n, const char *p1, const char *p2, const char *p3) {
        int ret;

        if (n < p1)
                ret = 1;
        else if (n > p1 && n < p2)
                ret = 2;
        else if (n > p2 && n < p3)
                ret = 3;
        else /* n > p3 */
                ret = 4;

        return ret;
}

static void
name_mode(const char *chan, char *mode, char *args) {
        Channel *c;
        Nick *n;
        char *m, *p, *c1, *c2, *c3, *s;
        int adding = 1;

        if (!(c = channel_find(chan)))
                return;

        if (!mode) /* invalid arguments */
                return;

        p = strtok(args, " ");
        if (p == NULL) /* none of the modes have arguments */
                return;

        /* find our comma delimiters. we can guarantee that all three
         * will be here from the parsing of the 005 line. */
        c1 = strchr(cmodes, ',');
        c2 = strchr(c1 + 1, ',');
        c3 = strchr(c2 + 1, ',');
        
        for (m = mode; *m; m++) {
                switch (*m) {
                case '+':
                        adding = 1;
                        break;
                case '-':
                        adding = 0;
                        break;
                default:
                        if (((s = strchr(cmodes, *m)) != NULL) && *m != ',') {
                                /* work out whether we need to skip arguments */
                                switch (ptr_split(s, c1, c2, c3)) {
                                case 1:
                                case 2:
                                        p = strtok(NULL, " ");
                                        break;
                                case 3: /* FALLTHROUGH */
                                        if (adding)
                                                p = strtok(NULL, " ");
                                case 4:
                                        break;
                                }
                        } else if ((s = strchr(umodes, *m)) != NULL) {
                                if (p == NULL) /* jumped off a cliff?? */
                                        return;

                                n = name_find(c, p);
                                if (n) {
                                        if (adding &&
                                            n->prefix == '\0')
                                                n->prefix = upref[s - umodes];
                                        else if (!adding &&
                                                 (n->prefix == upref[s - umodes])) {
                                                         n->prefix = '\0';
                                        }
                                }

                                p = strtok(NULL, " ");
                        }
                        
                        break;
                }
        }
}

static Nick *
name_find(Channel *c, const char *name)
{
        Nick *n;

        if (!c || !name)
                return NULL;
        
	for (n = c->nicks; n; n = n->next) {
		if (!strcmp(name, n->name))
                        return n; /* found */
	}
	return NULL;
}

static int
udsopen(const char *uds)
{
	struct sockaddr_un sun;
	size_t len;
	int fd;

	if ((fd = socket(AF_UNIX, SOCK_STREAM, 0)) == -1) {
		fprintf(stderr, "%s: socket: %s\n", argv0, strerror(errno));
		exit(1);
	}

	sun.sun_family = AF_UNIX;
	if (strlcpy(sun.sun_path, uds, sizeof(sun.sun_path)) >= sizeof(sun.sun_path)) {
		fprintf(stderr, "%s: UNIX domain socket path truncation\n", argv0);
		exit(1);
	}
	len = strlen(sun.sun_path) + 1 + sizeof(sun.sun_family);
	if (connect(fd, (struct sockaddr *)&sun, len) == -1) {
		fprintf(stderr, "%s: connect: %s\n", argv0, strerror(errno));
		exit(1);
	}
	return fd;
}

static int
tcpopen(const char *host, const char *service)
{
	struct addrinfo hints, *res = NULL, *rp;
	int fd = -1, e;

	memset(&hints, 0, sizeof(hints));
	hints.ai_family = AF_UNSPEC; /* allow IPv4 or IPv6 */
	hints.ai_flags = AI_NUMERICSERV; /* avoid name lookup for port */
	hints.ai_socktype = SOCK_STREAM;

	if ((e = getaddrinfo(host, service, &hints, &res))) {
		fprintf(stderr, "%s: getaddrinfo: %s\n", argv0, gai_strerror(e));
		exit(1);
	}

	for (rp = res; rp; rp = rp->ai_next) {
		fd = socket(res->ai_family, res->ai_socktype, res->ai_protocol);
		if (fd == -1)
			continue;
		if (connect(fd, res->ai_addr, res->ai_addrlen) == -1) {
			close(fd);
			fd = -1;
			continue;
		}
		break; /* success */
	}
	if (fd == -1) {
		fprintf(stderr, "%s: could not connect to %s:%s: %s\n",
			argv0, host, service, strerror(errno));
		exit(1);
	}

	freeaddrinfo(res);
	return fd;
}

static void
tokenize(char **result, char *str)
{
	char delim = ' ';
	char *p = NULL, *n = NULL;
	size_t i = 0;
	size_t reslen = TOK_LAST - TOK_CMD;
	size_t argoffset = TOK_ARG - TOK_CMD;
	size_t textoffset = TOK_TEXT - TOK_CMD;

	/* find the start of the command */
	for (n = str; *n == ' '; n++);

	p = n;
	while (*n != '\0') {
		if (i >= reslen) {
			return;
		} else if (i > argoffset && *n == delim && result[0]
		   && strtol(result[0], NULL, 10) > 0) {
			/* numeric command message, don't process any further */
			result[i++] = p;
			return;
		} else if (i < textoffset && *n == delim) {
			*n = '\0';
			result[i++] = p;
			p = ++n;

			if (*n == ':' && *(n+1) != '\0') {
				/* colon indicates start of command text */
				*n = '\0';
				result[textoffset] = n + 1;
				return;
			}
		} else {
			n++;
		}
	}

	/* add last entry */
	if (i < reslen && p < n && p && *p)
		result[i++] = p;

	return;
}

static void
channel_print(Channel *c, const char *buf)
{
	FILE *fp = NULL;
	time_t t = time(NULL);

	if (!(fp = fopen(c->outpath, "a")))
		return;
	fprintf(fp, "%lu %s\n", (unsigned long)t, buf);
	fclose(fp);
}

static void
cap_parse(char *buf) {
        char *p;

        p = strtok(buf, " ");
        
        while (p != NULL) {
                if (!strncmp("PREFIX=", p, 7)) {
                        p += 7;
                        parse_prefix(p);
                } else if (!strncmp("CHANMODES=", p, 10)) {
                        p += 10;
                        parse_cmodes(p);
                }

                p = strtok(NULL, " ");
        }
}

static void
parse_prefix(char *buf) {
        char *m, *p;
        size_t l, s;
        int i;

        /* validate the prefix string */
        m = buf;
        p = strchr(buf, ')');
        l = strlen(buf);
        if (l < 2 || *m != '(' || p == NULL || (p - m) * 2 != l)
                return;

        s = sizeof(upref);

        for (i=0, m++, p++; *m != ')' && i != (s - 1); m++, p++, i++) {
                umodes[i] = *m;
                upref[i] = *p;
        }
}

static void
parse_cmodes(char *buf) {
        char *p;
        int n = 0;

        /* validate the channel modes */
        for (p = buf; *p; p++) {
                if (*p == ',') {
                        n++;
                }
        }

        if (n < 3)
                return;

        strlcpy(cmodes, buf, sizeof(cmodes));
}


static void
proc_channels_privmsg(int ircfd, Channel *c, char *buf)
{
        Nick *n = NULL;

        if (trackprefix)
                n = name_find(c, nick);

        snprintf(msg, sizeof(msg), "<%s%s> %s",
                 n ? &n->prefix : "", nick, buf);
	channel_print(c, msg);
	snprintf(msg, sizeof(msg), "PRIVMSG %s :%s\r\n", c->name, buf);
	ewritestr(ircfd, msg);
}

static void
proc_channels_input(int ircfd, Channel *c, char *buf)
{
        Channel * tmp;
        char *p = NULL;
	size_t buflen;

	if (buf[0] == '\0')
		return;
	if (buf[0] != '/') {
		proc_channels_privmsg(ircfd, c, buf);
		return;
	}

	msg[0] = '\0';
	if ((buflen = strlen(buf)) < 2)
		return;
	if (buf[2] == ' ' || buf[2] == '\0') {
		switch (buf[1]) {
		case 'j': /* join */
			if (buflen < 3)
				return;
			if ((p = strchr(&buf[3], ' '))) /* password parameter */
				*p = '\0';
			if ((buf[3] == '#') || (buf[3] == '&') || (buf[3] == '+') ||
				(buf[3] == '!'))
			{
				/* password protected channel */
				if (p)
					snprintf(msg, sizeof(msg), "JOIN %s %s\r\n", &buf[3], p + 1);
				else
					snprintf(msg, sizeof(msg), "JOIN %s\r\n", &buf[3]);
				channel_join(&buf[3]);
			} else if (buflen >= 3) {
                                c = channel_join(&buf[3]);

                                if (p)
                                        proc_channels_privmsg(ircfd, c, p + 1);
                                
				return;
                        }
			break;
		case 't': /* topic */
			if (buflen >= 3)
				snprintf(msg, sizeof(msg), "TOPIC %s :%s\r\n", c->name, &buf[3]);
			break;
		case 'a': /* away */
			if (buflen >= 3) {
				snprintf(msg, sizeof(msg), "-!- %s is away \"%s\"", nick, &buf[3]);
				channel_print(c, msg);
			}
			if (buflen >= 3)
				snprintf(msg, sizeof(msg), "AWAY :%s\r\n", &buf[3]);
			else
				snprintf(msg, sizeof(msg), "AWAY\r\n");
			break;
		case 'n': /* change nick */
			if (buflen >= 3) {
				strlcpy(_nick, &buf[3], sizeof(_nick));
				snprintf(msg, sizeof(msg), "NICK %s\r\n", &buf[3]);
			}
			break;
		case 'l': /* leave */
			if (c == channelmaster)
				return;
			if (buflen >= 3)
				snprintf(msg, sizeof(msg), "PART %s :%s\r\n", c->name, &buf[3]);
			else
				snprintf(msg, sizeof(msg),
                                         "PART %s :leaving\r\n", c->name);
                        if ((c->name[0] == '#') || (c->name[0] == '&') ||
                            (c->name[0] == '+') || (c->name[0] == '!')) {
                                    ewritestr(ircfd, msg);
                                    if (buflen >= 3) {
                                            snprintf(msg, sizeof(msg),
                                                     "-!- Leaving %s: \"%s\"",
                                                     c->name, &buf[3]);
                                    } else {
                                            snprintf(msg, sizeof(msg),
                                                     "-!- Leaving %s: \"leaving\"",
                                                     c->name);
                                    }
                                    channel_print(c, msg);
                        }
			channel_leave(c);
			return;
                        break;
                case 'o': /* notice */
                        if (c == channelmaster)
                                return;
			if (buflen >= 3) {
				snprintf(msg, sizeof(msg), "-!- -> \"%s\"", &buf[3]);
				channel_print(c, msg);
			}
			if (buflen >= 3)
				snprintf(msg, sizeof(msg), "NOTICE %s :%s\r\n", c->name, &buf[3]);
			break;
		case 'q': /* quit */
			if (buflen >= 3)
				snprintf(msg, sizeof(msg), "QUIT :%s\r\n", &buf[3]);
			else
				snprintf(msg, sizeof(msg),
				         "QUIT %s\r\n", "bye");
                        ewritestr(ircfd, msg);

			if (buflen >= 3)
                                snprintf(msg, sizeof(msg), "-!- Quitting: %s", &buf[3]);
			else
				snprintf(msg, sizeof(msg),
                                         "-!- Quitting: %s", "bye");

                        for (c = channels; c; c = tmp) {
                                tmp = c->next;
                                channel_print(c, msg);
                        }
                        
			isrunning = 0;
			return;
			break;
		default: /* raw IRC command */
			snprintf(msg, sizeof(msg), "%s\r\n", &buf[1]);
			break;
		}
	} else {
		/* raw IRC command */
		snprintf(msg, sizeof(msg), "%s\r\n", &buf[1]);
	}
	if (msg[0] != '\0')
		ewritestr(ircfd, msg);
}

static void
proc_server_cmd(int fd, char *buf)
{
	Channel *c;
	const char *channel;
	char *argv[TOK_LAST], *cmd = NULL, *p = NULL;
        unsigned int i;
        int isnotice = 0, isprivmsg = 0;

	if (!buf || buf[0] == '\0')
		return;

	/* clear tokens */
	for (i = 0; i < TOK_LAST; i++)
		argv[i] = NULL;

	/* check prefix */
	if (buf[0] == ':') {
		if (!(p = strchr(buf, ' ')))
			return;
		*p = '\0';
		for (++p; *p == ' '; p++)
			;
		cmd = p;
		argv[TOK_NICKSRV] = &buf[1];
		if ((p = strchr(buf, '!'))) {
			*p = '\0';
			argv[TOK_USER] = ++p;
		}
	} else {
		cmd = buf;
	}

	/* remove CRLFs */
	for (p = cmd; p && *p != '\0'; p++) {
		if (*p == '\r' || *p == '\n')
			*p = '\0';
	}

	tokenize(&argv[TOK_CMD], cmd);

	if (!argv[TOK_CMD] || !strcmp("PONG", argv[TOK_CMD])) {
                return;                
	} else if (!strcmp("PING", argv[TOK_CMD])) {
		snprintf(msg, sizeof(msg), "PONG %s\r\n", argv[TOK_TEXT]);
		ewritestr(fd, msg);
                return;
        } else if (!strncmp("353", argv[TOK_CMD], 4)) {
		p = strtok(argv[TOK_ARG]," ");
		if(!(p = strtok(NULL," ")))
			return;
		snprintf(msg, sizeof(msg), "%s%s", argv[TOK_ARG] ? argv[TOK_ARG] : "", argv[TOK_TEXT] ? argv[TOK_TEXT] : "");
                channel_print(channelmaster, msg);
                proc_names(p, argv[TOK_TEXT]);
                return;
        } else if (!strncmp("005", argv[TOK_CMD], 4)) {
		/* the tokeniser can't split 005 lines properly while handling
		 * other numerics in the general case */
		snprintf(msg, sizeof(msg), "%s %s",
			 	argv[TOK_ARG] ? argv[TOK_ARG] : "",
				argv[TOK_TEXT] ? argv[TOK_TEXT] : "");
		channel_print(channelmaster, msg);
                cap_parse(argv[TOK_ARG]);
                cap_parse(argv[TOK_TEXT]);
                return;
        } else if (!strcmp("MODE", argv[TOK_CMD])) { /* servers can send channel MODEs and KICKs */
		snprintf(msg, sizeof(msg), "-!- %s changed mode/%s -> %s %s",
				argv[TOK_NICKSRV],
				argv[TOK_CHAN] ? argv[TOK_CHAN] : "",
				argv[TOK_ARG]  ? argv[TOK_ARG] : "",
                                argv[TOK_TEXT] ? argv[TOK_TEXT] : "");
                if (trackprefix) name_mode(argv[TOK_CHAN], argv[TOK_ARG], argv[TOK_TEXT]);
	} else if (!strcmp("KICK", argv[TOK_CMD]) && argv[TOK_ARG]) {
		snprintf(msg, sizeof(msg), "-!- %s kicked %s (\"%s\")",
			 	argv[TOK_NICKSRV], argv[TOK_ARG],
			 	argv[TOK_TEXT] ? argv[TOK_TEXT] : "");
		name_rm(argv[TOK_CHAN], argv[TOK_ARG]);
	} else if (!strcmp("TOPIC", argv[TOK_CMD])) { /* servers can also send TOPIC lines (cf. recovering from netsplit) */
		snprintf(msg, sizeof(msg), "-!- %s changed topic to \"%s\"",
				argv[TOK_NICKSRV],
				argv[TOK_TEXT] ? argv[TOK_TEXT] : "");
        } else if (!argv[TOK_NICKSRV] || !argv[TOK_USER]) {
                /* server message */
		snprintf(msg, sizeof(msg), "%s%s%s",
			 	argv[TOK_ARG] ? argv[TOK_ARG] : "",
			 	argv[TOK_ARG] && argv[TOK_TEXT] ? " " : "",
				argv[TOK_TEXT] ? argv[TOK_TEXT] : "");
		channel_print(channelmaster, msg);
		return; /* don't process further */
	} else if (!strcmp("ERROR", argv[TOK_CMD]))
		snprintf(msg, sizeof(msg), "-!- error %s",
				argv[TOK_TEXT] ? argv[TOK_TEXT] : "unknown");
	else if (!strcmp("JOIN", argv[TOK_CMD]) && (argv[TOK_CHAN] || argv[TOK_TEXT])) {
		if (argv[TOK_TEXT])
                        argv[TOK_CHAN] = argv[TOK_TEXT];
                snprintf(msg, sizeof(msg), "-!- %s(%s) has joined %s",
                         argv[TOK_NICKSRV], argv[TOK_USER], argv[TOK_CHAN]);
                name_add(argv[TOK_CHAN], argv[TOK_NICKSRV]);
        } else if (!strcmp("PART", argv[TOK_CMD]) && argv[TOK_CHAN]) {
		snprintf(msg, sizeof(msg), "-!- %s(%s) has left %s: \"%s\"",
			 argv[TOK_NICKSRV], argv[TOK_USER], argv[TOK_CHAN],
			 argv[TOK_TEXT] ? argv[TOK_TEXT] : "");
		/* if user itself leaves, don't write to channel (don't reopen channel). */
		if (!strcmp(argv[TOK_NICKSRV], nick))
			return;
                name_rm(argv[TOK_CHAN], argv[TOK_NICKSRV]);
	} else if (!strcmp("QUIT", argv[TOK_CMD])) {
		snprintf(msg, sizeof(msg), "-!- %s(%s) has quit \"%s\"",
				argv[TOK_NICKSRV], argv[TOK_USER],
                                argv[TOK_TEXT] ? argv[TOK_TEXT] : "");
                name_quit(argv[TOK_NICKSRV], argv[TOK_USER], argv[TOK_TEXT]);
                return;
	} else if (!strncmp("NICK", argv[TOK_CMD], 5) && argv[TOK_TEXT] &&
	          !strcmp(_nick, argv[TOK_TEXT])) {
		strlcpy(nick, _nick, sizeof(nick));
		snprintf(msg, sizeof(msg), "-!- changed nick to \"%s\"", nick);
                name_menick(argv[TOK_NICKSRV], argv[TOK_TEXT]);
                return;
	} else if (!strcmp("NICK", argv[TOK_CMD]) && argv[TOK_TEXT]) {
		snprintf(msg, sizeof(msg), "-!- %s changed nick to %s",
                         argv[TOK_NICKSRV], argv[TOK_TEXT]);
                name_nick(argv[TOK_NICKSRV], argv[TOK_TEXT]);
                return;
        } else if (!strcmp("NOTICE", argv[TOK_CMD])) {
                isnotice = 1; /* this is a hack, as we need to know who/what
                               * we're sending to before we can format the
                               * message */
        } else if (!strcmp("PRIVMSG", argv[TOK_CMD])) {
                isprivmsg = 1; /* hack, as above. */
	} else {
		return; /* can't read this message */
	}
        if (argv[TOK_CHAN] && !strcmp(argv[TOK_CHAN], nick)) {
                channel = argv[TOK_NICKSRV];

                if (isnotice)
                        snprintf(msg, sizeof(msg), "-!- \"%s\"",
                                 argv[TOK_TEXT] ? argv[TOK_TEXT] : "");
                else if (isprivmsg)
                        snprintf(msg, sizeof(msg), "<%s> %s", argv[TOK_NICKSRV],
                                 argv[TOK_TEXT] ? argv[TOK_TEXT] : "");
        } else {
                channel = argv[TOK_CHAN];
                Nick *n = NULL;

                if (trackprefix)
                        n = name_find(channel_find(channel), argv[TOK_NICKSRV]);
                
                if (isnotice)
                        snprintf(msg, sizeof(msg), "-!- %s%s/%s -> \"%s\"",
                                 n ? &n->prefix : "",
                                 argv[TOK_NICKSRV] ? argv[TOK_NICKSRV] : "",
                                 channel, argv[TOK_TEXT] ? argv[TOK_TEXT] : "");
                else if (isprivmsg) {
                        snprintf(msg, sizeof(msg), "<%s%s> %s", n ? &n->prefix : "",
                                 argv[TOK_NICKSRV],
                                 argv[TOK_TEXT] ? argv[TOK_TEXT] : "");
                }
        }

	if (!channel || channel[0] == '\0')
		c = channelmaster;
	else
		c = channel_join(channel);
	if (c)
		channel_print(c, msg);
}

static void
proc_names(const char *chan, char *names) {
	char *p;

        if(!(p = strtok(names," ")))
                return;
	do {
		name_add(chan,p);
	} while((p = strtok(NULL," ")));
}

static int
read_line(int fd, char *buf, size_t bufsiz)
{
	size_t i = 0;
	char c = '\0';

	do {
		if (read(fd, &c, sizeof(char)) != sizeof(char))
			return -1;
		buf[i++] = c;
	} while (c != '\n' && i < bufsiz);
	buf[i - 1] = '\0'; /* eliminates '\n' */
	return 0;
}

static void
handle_channels_input(int ircfd, Channel *c)
{
	char buf[IRC_MSG_MAX];

	if (read_line(c->fdin, buf, sizeof(buf)) == -1) {
		if (channel_reopen(c) == -1)
			channel_rm(c);
		return;
	}
	proc_channels_input(ircfd, c, buf);
}

static void
handle_server_output(int infd, int outfd)
{
	char buf[IRC_MSG_MAX];

	if (read_line(infd, buf, sizeof(buf)) == -1) {
		fprintf(stderr, "%s: remote host closed connection: %s\n",
		        argv0, strerror(errno));
		exit(1);
	}
	fprintf(stdout, "%lu %s\n", (unsigned long)time(NULL), buf);
	fflush(stdout);
	proc_server_cmd(outfd, buf);
}

static void
sighandler(int sig)
{
	if (sig == SIGTERM || sig == SIGINT)
		isrunning = 0;
}

static void
setup(void)
{
	struct sigaction sa;

	memset(&sa, 0, sizeof(sa));
	sa.sa_handler = sighandler;
	sigaction(SIGTERM, &sa, NULL);
        sigaction(SIGINT, &sa, NULL);

        /* default values for prefixes and channel modes. these need
         * to be tracked regardless of whether we're keeping track of
         * people's modes, because we still need to know what the prefix
         * chars so we can skip them. */
        parse_prefix("(qaohv)~&@%+");
        parse_cmodes("beI,k,l,imMnOPQRstVz");
}

static void
run(int ircinfd, int ircoutfd, const char *host)
{
	Channel *c, *tmp;
	fd_set rdset;
	struct timeval tv;
	char ping_msg[IRC_MSG_MAX];
	int r, maxfd;

	snprintf(ping_msg, sizeof(ping_msg), "PING %s\r\n", host);
	while (isrunning) {
                maxfd = ircinfd > ircoutfd ? ircinfd : ircoutfd;
		FD_ZERO(&rdset);
		FD_SET(ircinfd, &rdset);
		for (c = channels; c; c = c->next) {
			if (c->fdin > maxfd)
				maxfd = c->fdin;
			FD_SET(c->fdin, &rdset);
		}
		memset(&tv, 0, sizeof(tv));
		tv.tv_sec = 120;
		r = select(maxfd + 1, &rdset, 0, 0, &tv);
		if (r < 0) {
			if (errno == EINTR)
				continue;
			fprintf(stderr, "%s: select: %s\n", argv0, strerror(errno));
			exit(1);
		} else if (r == 0) {
			if (time(NULL) - last_response >= PING_TIMEOUT) {
                                for (c = channels; c; c = tmp) {
                                        tmp = c->next;
                                        channel_print(c, "-!- ii shutting down: ping timeout");
                                }
				exit(2); /* status code 2 for timeout */
			}
			ewritestr(ircoutfd, ping_msg);
			continue;
		}
		if (FD_ISSET(ircinfd, &rdset)) {
			handle_server_output(ircinfd, ircoutfd);
			last_response = time(NULL);
		}
		for (c = channels; c; c = tmp) {
			tmp = c->next;
			if (FD_ISSET(c->fdin, &rdset))
				handle_channels_input(ircoutfd, c);
		}
	}
}

int
main(int argc, char *argv[])
{
	Channel *c, *tmp;
	struct passwd *spw;
        const char *key = NULL, *username = NULL, *fullname = NULL;
        const char *host = "", *uds = NULL, *service = "6667";
	char prefix[PATH_MAX];
        int ircinfd, ircoutfd, r;
        int ucspi = 0;

	/* use nickname and home dir of user by default */
	if (!(spw = getpwuid(getuid()))) {
		fprintf(stderr, "%s: getpwuid: %s\n", argv0, strerror(errno));
		exit(1);
	}
	strlcpy(nick, spw->pw_name, sizeof(nick));
	snprintf(prefix, sizeof(prefix), "%s/irc", spw->pw_dir);

        username = nick;
        
	ARGBEGIN {
	case 'f':
		fullname = EARGF(usage());
		break;
	case 'i':
		strlcpy(prefix, EARGF(usage()), sizeof(prefix));
		break;
	case 'k':
		key = getenv(EARGF(usage()));
		break;
	case 'n':
		strlcpy(nick, EARGF(usage()), sizeof(nick));
		break;
	case 'p':
		service = EARGF(usage());
		break;
	case 's':
		host = EARGF(usage());
                break;
        case 'u':
                username = EARGF(usage());
                break;
	case 'U':
		uds = EARGF(usage());
                break;
        case 't':
                ucspi = 1;
                break;
        case 'P':
                trackprefix = 0;
                break;
	default:
		usage();
		break;
	} ARGEND;

	if (!*host)
		usage();

	if (uds)
                ircinfd = ircoutfd = udsopen(uds);
        else if (ucspi) {
                ircinfd = READ_FD;
                ircoutfd = WRITE_FD;
        } else
		ircinfd = ircoutfd = tcpopen(host, service);

#ifdef __OpenBSD__
	/* OpenBSD pledge(2) support */
	if (pledge("stdio rpath wpath cpath dpath", NULL) == -1) {
		fprintf(stderr, "%s: pledge: %s\n", argv0, strerror(errno));
		exit(1);
	}
#endif

	r = snprintf(ircpath, sizeof(ircpath), "%s/%s", prefix, host);
	if (r < 0 || (size_t)r >= sizeof(ircpath)) {
		fprintf(stderr, "%s: path to irc directory too long\n", argv0);
		exit(1);
	}
	create_dirtree(ircpath);

	channelmaster = channel_add(""); /* master channel */
	if (key)
		loginkey(ircoutfd, key);
	loginuser(ircoutfd, host, username, fullname && *fullname ? fullname : username);
	setup();
	run(ircinfd, ircoutfd, host);
	if (channelmaster)
		channel_leave(channelmaster);

	for (c = channels; c; c = tmp) {
		tmp = c->next;
		channel_leave(c);
	}

	return 0;
}
