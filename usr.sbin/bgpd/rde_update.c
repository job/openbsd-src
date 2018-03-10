/*	$OpenBSD: rde_update.c,v 1.89 2018/02/10 05:54:31 claudio Exp $ */

/*
 * Copyright (c) 2004 Claudio Jeker <claudio@openbsd.org>
 *
 * Permission to use, copy, modify, and distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 * ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 * ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 * OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 */
#include <sys/types.h>
#include <sys/queue.h>

#include <limits.h>
#include <stdlib.h>
#include <string.h>
#include <siphash.h>

#include "bgpd.h"
#include "rde.h"
#include "log.h"

void
up_init(struct rde_peer *peer)
{
	u_int8_t	i;

	for (i = 0; i < AID_MAX; i++) {
		TAILQ_INIT(&peer->updates[i]);
		TAILQ_INIT(&peer->withdraws[i]);
	}
	peer->up_pcnt = 0;
	peer->up_acnt = 0;
	peer->up_nlricnt = 0;
	peer->up_wcnt = 0;
}

void
up_down(struct rde_peer *peer)
{
	struct prefix	*p;
	u_int8_t	i;

	for (i = 0; i < AID_MAX; i++)
		while ((p = TAILQ_FIRST(&peer->withdraws[i])) != NULL)
			prefix_destroy(p);

	peer->up_pcnt = 0;
	peer->up_acnt = 0;
	peer->up_nlricnt = 0;
	peer->up_wcnt = 0;
}

int
up_test_update(struct rde_peer *peer, struct prefix *p)
{
	struct bgpd_addr	 addr;
	struct rde_aspath	*asp;
	struct rde_peer		*prefp;
	struct attr		*attr;

	if (peer->state != PEER_UP)
		return (-1);

	if (p == NULL)
		/* no prefix available */
		return (0);

	prefp = prefix_peer(p);
	asp = prefix_aspath(p);

	if (peer == prefp)
		/* Do not send routes back to sender */
		return (0);

	if (asp->flags & F_ATTR_PARSE_ERR)
		fatalx("try to send out a botched path");
	if (asp->flags & F_ATTR_LOOP)
		fatalx("try to send out a looped path");

	pt_getaddr(p->re->prefix, &addr);
	if (peer->capa.mp[addr.aid] == 0)
		return (-1);

	if (!prefp->conf.ebgp && !peer->conf.ebgp) {
		/*
		 * route reflector redistribution rules:
		 * 1. if announce is set                -> announce
		 * 2. old non-client, new non-client    -> no
		 * 3. old client, new non-client        -> yes
		 * 4. old non-client, new client        -> yes
		 * 5. old client, new client            -> yes
		 */
		if (prefp->conf.reflector_client == 0 &&
		    peer->conf.reflector_client == 0 &&
		    (asp->flags & F_PREFIX_ANNOUNCED) == 0)
			/* Do not redistribute updates to ibgp peers */
			return (0);
	}

	/* announce type handling */
	switch (peer->conf.announce_type) {
	case ANNOUNCE_UNDEF:
	case ANNOUNCE_NONE:
	case ANNOUNCE_DEFAULT_ROUTE:
		/*
		 * no need to withdraw old prefix as this will be
		 * filtered out as well.
		 */
		return (-1);
	case ANNOUNCE_ALL:
		break;
	case ANNOUNCE_SELF:
		/*
		 * pass only prefix that have an aspath count
		 * of zero this is equal to the ^$ regex.
		 */
		if (asp->aspath->ascnt != 0)
			return (0);
		break;
	}

	/* well known communities */
	if (community_match(asp, COMMUNITY_WELLKNOWN, COMMUNITY_NO_ADVERTISE))
		return (0);
	if (peer->conf.ebgp && community_match(asp, COMMUNITY_WELLKNOWN,
	    COMMUNITY_NO_EXPORT))
		return (0);
	if (peer->conf.ebgp && community_match(asp, COMMUNITY_WELLKNOWN,
	    COMMUNITY_NO_EXPSUBCONFED))
		return (0);

	/*
	 * Don't send messages back to originator
	 * this is not specified in the RFC but seems logical.
	 */
	if ((attr = attr_optget(asp, ATTR_ORIGINATOR_ID)) != NULL) {
		if (memcmp(attr->data, &peer->remote_bgpid,
		    sizeof(peer->remote_bgpid)) == 0) {
			/* would cause loop don't send */
			return (-1);
		}
	}

	return (1);
}

void
up_generate_updates(struct filter_head *rules, struct rde_peer *peer,
    struct prefix *new, struct prefix *old)
{
	struct rde_aspath		*fasp;
	struct bgpd_addr		 addr;

	if (peer->state != PEER_UP)
		return;

	if (new == NULL) {
withdraw:
		if (up_test_update(peer, old) != 1)
			return;

		pt_getaddr(old->re->prefix, &addr);
		if (rde_filter(rules, NULL, peer, prefix_aspath(old), &addr,
		    old->re->prefix->prefixlen, prefix_peer(old)) ==
		    ACTION_DENY)
			return;

		prefix_withdraw(&ribs[RIB_ADJ_OUT].rib, peer, &addr,
		    old->re->prefix->prefixlen);
	} else {
		switch (up_test_update(peer, new)) {
		case 1:
			break;
		case 0:
			goto withdraw;
		case -1:
			return;
		}

		pt_getaddr(new->re->prefix, &addr);
		if (rde_filter(rules, &fasp, peer, prefix_aspath(new), &addr,
		    new->re->prefix->prefixlen, prefix_peer(new)) ==
		    ACTION_DENY) {
			path_put(fasp);
			goto withdraw;
		}
		if (fasp == NULL)
			fasp = prefix_aspath(new);

		path_update(&ribs[RIB_ADJ_OUT].rib, peer, fasp, &addr,
		    new->re->prefix->prefixlen, F_ATTR_UPDATE);

		/* free modified aspath */
		if (fasp != prefix_aspath(new))
			path_put(fasp);
	}
}

/* send a default route to the specified peer */
void
up_generate_default(struct filter_head *rules, struct rde_peer *peer,
    u_int8_t aid)
{
	struct rde_aspath	*asp, *fasp;
	struct bgpd_addr	 addr;

	if (peer->capa.mp[aid] == 0)
		return;

	asp = path_get();
	asp->aspath = aspath_get(NULL, 0);
	asp->origin = ORIGIN_IGP;
	asp->aid = aid;
	/* the other default values are OK, nexthop is once again NULL */

	/*
	 * XXX apply default overrides. Not yet possible, mainly a parse.y
	 * problem.
	 */
	/* rde_apply_set(asp, set, af, NULL ???, DIR_IN); */

	/* filter as usual */
	bzero(&addr, sizeof(addr));
	addr.aid = aid;

	if (rde_filter(rules, &fasp, peer, asp, &addr, 0, NULL) ==
	    ACTION_DENY) {
		path_put(fasp);
		path_put(asp);
		return;
	}

	if (fasp == NULL)
		fasp = asp;

	path_update(&ribs[RIB_ADJ_OUT].rib, peer, fasp, &addr, 0,
	    F_ATTR_UPDATE);

	/* no longer needed */
	if (fasp != asp)
		path_put(fasp);
	path_put(asp);
}

int
up_generate_marker(struct rde_peer *peer, u_int8_t aid)
{
	struct rde_aspath	*asp;
	struct aspath_queue	*upl;

	asp = path_get_eor(peer, aid);

	upl = &peer->updates[aid];
	TAILQ_INSERT_TAIL(upl, asp, update_l);
	asp->flags |= F_ATTR_UPDATE;
	peer->up_acnt++;

	return (0);
}

/* only for IPv4 */
static in_addr_t
up_get_nexthop(struct rde_peer *peer, struct rde_aspath *a)
{
	in_addr_t	mask;

	/* nexthop, already network byte order */
	if (a->flags & F_NEXTHOP_NOMODIFY) {
		/* no modify flag set */
		if (a->nexthop == NULL)
			return (peer->local_v4_addr.v4.s_addr);
		else
			return (a->nexthop->exit_nexthop.v4.s_addr);
	} else if (a->flags & F_NEXTHOP_SELF)
		return (peer->local_v4_addr.v4.s_addr);
	else if (!peer->conf.ebgp) {
		/*
		 * If directly connected use peer->local_v4_addr
		 * this is only true for announced networks.
		 */
		if (a->nexthop == NULL)
			return (peer->local_v4_addr.v4.s_addr);
		else if (a->nexthop->exit_nexthop.v4.s_addr ==
		    peer->remote_addr.v4.s_addr)
			/*
			 * per RFC: if remote peer address is equal to
			 * the nexthop set the nexthop to our local address.
			 * This reduces the risk of routing loops.
			 */
			return (peer->local_v4_addr.v4.s_addr);
		else
			return (a->nexthop->exit_nexthop.v4.s_addr);
	} else if (peer->conf.distance == 1) {
		/* ebgp directly connected */
		if (a->nexthop != NULL &&
		    a->nexthop->flags & NEXTHOP_CONNECTED) {
			mask = htonl(
			    prefixlen2mask(a->nexthop->nexthop_netlen));
			if ((peer->remote_addr.v4.s_addr & mask) ==
			    (a->nexthop->nexthop_net.v4.s_addr & mask))
				/* nexthop and peer are in the same net */
				return (a->nexthop->exit_nexthop.v4.s_addr);
			else
				return (peer->local_v4_addr.v4.s_addr);
		} else
			return (peer->local_v4_addr.v4.s_addr);
	} else
		/* ebgp multihop */
		/*
		 * For ebgp multihop nh->flags should never have
		 * NEXTHOP_CONNECTED set so it should be possible to unify the
		 * two ebgp cases. But this is safe and RFC compliant.
		 */
		return (peer->local_v4_addr.v4.s_addr);
}

static int
up_generate_mp_reach(u_char *buf, int len, struct rde_peer *peer,
    struct rde_aspath *a, u_int8_t aid)
{
	u_char		*attrbuf;
	int		 r, wpos, attrlen;
	u_int16_t	 tmp;

	if (len < 4)
		return (-1);
	/* attribute header, defaulting to extended length one */
	buf[0] = ATTR_OPTIONAL | ATTR_EXTLEN;
	buf[1] = ATTR_MP_REACH_NLRI;
	wpos = 4;
	attrbuf = buf + wpos;

	switch (aid) {
	case AID_INET6:
		attrlen = 21; /* AFI + SAFI + NH LEN + NH + Reserved */
		if (len < wpos + attrlen)
			return (-1);
		wpos += attrlen;
		if (aid2afi(aid, &tmp, &attrbuf[2]))
			fatalx("up_generate_mp_reach: bad AID");
		tmp = htons(tmp);
		memcpy(attrbuf, &tmp, sizeof(tmp));
		attrbuf[3] = sizeof(struct in6_addr);
		attrbuf[20] = 0; /* Reserved must be 0 */

		/* nexthop dance see also up_get_nexthop() */
		attrbuf += 4;
		if (a->flags & F_NEXTHOP_NOMODIFY) {
			/* no modify flag set */
			if (a->nexthop == NULL)
				memcpy(attrbuf, &peer->local_v6_addr.v6,
				    sizeof(struct in6_addr));
			else
				memcpy(attrbuf, &a->nexthop->exit_nexthop.v6,
				    sizeof(struct in6_addr));
		} else if (a->flags & F_NEXTHOP_SELF)
			memcpy(attrbuf, &peer->local_v6_addr.v6,
			    sizeof(struct in6_addr));
		else if (!peer->conf.ebgp) {
			/* ibgp */
			if (a->nexthop == NULL ||
			    (a->nexthop->exit_nexthop.aid == AID_INET6 &&
			    !memcmp(&a->nexthop->exit_nexthop.v6,
			    &peer->remote_addr.v6, sizeof(struct in6_addr))))
				memcpy(attrbuf, &peer->local_v6_addr.v6,
				    sizeof(struct in6_addr));
			else
				memcpy(attrbuf, &a->nexthop->exit_nexthop.v6,
				    sizeof(struct in6_addr));
		} else if (peer->conf.distance == 1) {
			/* ebgp directly connected */
			if (a->nexthop != NULL &&
			    a->nexthop->flags & NEXTHOP_CONNECTED)
				if (prefix_compare(&peer->remote_addr,
				    &a->nexthop->nexthop_net,
				    a->nexthop->nexthop_netlen) == 0) {
					/*
					 * nexthop and peer are in the same
					 * subnet
					 */
					memcpy(attrbuf,
					    &a->nexthop->exit_nexthop.v6,
					    sizeof(struct in6_addr));
					break;
				}
			memcpy(attrbuf, &peer->local_v6_addr.v6,
			    sizeof(struct in6_addr));
		} else
			/* ebgp multihop */
			memcpy(attrbuf, &peer->local_v6_addr.v6,
			    sizeof(struct in6_addr));
		break;
	case AID_VPN_IPv4:
		attrlen = 17; /* AFI + SAFI + NH LEN + NH + Reserved */
		if (len < wpos + attrlen)
			return (-1);
		wpos += attrlen;
		if (aid2afi(aid, &tmp, &attrbuf[2]))
			fatalx("up_generate_mp_reachi: bad AID");
		tmp = htons(tmp);
		memcpy(attrbuf, &tmp, sizeof(tmp));
		attrbuf[3] = sizeof(u_int64_t) + sizeof(struct in_addr);
		bzero(attrbuf + 4, sizeof(u_int64_t));

		/* nexthop dance see also up_get_nexthop() */
		attrbuf += 12;
		if (a->flags & F_NEXTHOP_NOMODIFY) {
			/* no modify flag set */
			if (a->nexthop == NULL)
				memcpy(attrbuf, &peer->local_v4_addr.v4,
				    sizeof(struct in_addr));
			else
				/* nexthops are stored as IPv4 addrs */
				memcpy(attrbuf, &a->nexthop->exit_nexthop.v4,
				    sizeof(struct in_addr));
		} else if (a->flags & F_NEXTHOP_SELF)
			memcpy(attrbuf, &peer->local_v4_addr.v4,
			    sizeof(struct in_addr));
		else if (!peer->conf.ebgp) {
			/* ibgp */
			if (a->nexthop == NULL ||
			    (a->nexthop->exit_nexthop.aid == AID_INET &&
			    !memcmp(&a->nexthop->exit_nexthop.v4,
			    &peer->remote_addr.v4, sizeof(struct in_addr))))
				memcpy(attrbuf, &peer->local_v4_addr.v4,
				    sizeof(struct in_addr));
			else
				memcpy(attrbuf, &a->nexthop->exit_nexthop.v4,
				    sizeof(struct in_addr));
		} else if (peer->conf.distance == 1) {
			/* ebgp directly connected */
			if (a->nexthop != NULL &&
			    a->nexthop->flags & NEXTHOP_CONNECTED)
				if (prefix_compare(&peer->remote_addr,
				    &a->nexthop->nexthop_net,
				    a->nexthop->nexthop_netlen) == 0) {
					/*
					 * nexthop and peer are in the same
					 * subnet
					 */
					memcpy(attrbuf,
					    &a->nexthop->exit_nexthop.v4,
					    sizeof(struct in_addr));
					break;
				}
			memcpy(attrbuf, &peer->local_v4_addr.v4,
			    sizeof(struct in_addr));
		} else
			/* ebgp multihop */
			memcpy(attrbuf, &peer->local_v4_addr.v4,
			    sizeof(struct in_addr));
		break;
	default:
		fatalx("up_generate_mp_reach: unknown AID");
	}

	r = up_dump_prefix(buf + wpos, len - wpos, &a->updates, peer, 0);
	if (r == 0) {
		/* no prefixes written ... */
		return (-1);
	}
	attrlen += r;
	wpos += r;
	/* update attribute length field */
	tmp = htons(attrlen);
	memcpy(buf + 2, &tmp, sizeof(tmp));

	return (wpos);
}

static int
up_generate_attr(u_char *buf, int len, struct rde_peer *peer,
    struct rde_aspath *a, u_int8_t aid)
{
	struct attr	*oa, *newaggr = NULL;
	u_char		*pdata;
	u_int32_t	 tmp32;
	in_addr_t	 nexthop;
	int		 flags, r, neednewpath = 0;
	u_int16_t	 wlen = 0, plen;
	u_int8_t	 l;
	u_int16_t	 nlen = 0;
	u_char		*ndata = NULL;

	/* origin */
	if ((r = attr_write(buf + wlen, len, ATTR_WELL_KNOWN,
	    ATTR_ORIGIN, &a->origin, 1)) == -1)
		return (-1);
	wlen += r; len -= r;

	/* aspath */
	if (!peer->conf.ebgp ||
	    peer->conf.flags & PEERFLAG_TRANS_AS)
		pdata = aspath_prepend(a->aspath, peer->conf.local_as, 0,
		    &plen);
	else
		pdata = aspath_prepend(a->aspath, peer->conf.local_as, 1,
		    &plen);

	if (!rde_as4byte(peer))
		pdata = aspath_deflate(pdata, &plen, &neednewpath);

	if ((r = attr_write(buf + wlen, len, ATTR_WELL_KNOWN,
	    ATTR_ASPATH, pdata, plen)) == -1)
		return (-1);
	wlen += r; len -= r;
	free(pdata);

	switch (aid) {
	case AID_INET:
		nexthop = up_get_nexthop(peer, a);
		if ((r = attr_write(buf + wlen, len, ATTR_WELL_KNOWN,
		    ATTR_NEXTHOP, &nexthop, 4)) == -1)
			return (-1);
		wlen += r; len -= r;
		break;
	default:
		break;
	}

	/*
	 * The old MED from other peers MUST not be announced to others
	 * unless the MED is originating from us or the peer is an IBGP one.
	 * Only exception are routers with "transparent-as yes" set.
	 */
	if (a->flags & F_ATTR_MED && (!peer->conf.ebgp ||
	    a->flags & F_ATTR_MED_ANNOUNCE ||
	    peer->conf.flags & PEERFLAG_TRANS_AS)) {
		tmp32 = htonl(a->med);
		if ((r = attr_write(buf + wlen, len, ATTR_OPTIONAL,
		    ATTR_MED, &tmp32, 4)) == -1)
			return (-1);
		wlen += r; len -= r;
	}

	if (!peer->conf.ebgp) {
		/* local preference, only valid for ibgp */
		tmp32 = htonl(a->lpref);
		if ((r = attr_write(buf + wlen, len, ATTR_WELL_KNOWN,
		    ATTR_LOCALPREF, &tmp32, 4)) == -1)
			return (-1);
		wlen += r; len -= r;
	}

	/*
	 * dump all other path attributes. Following rules apply:
	 *  1. well-known attrs: ATTR_ATOMIC_AGGREGATE and ATTR_AGGREGATOR
	 *     pass unmodified (enforce flags to correct values)
	 *     Actually ATTR_AGGREGATOR may be deflated for OLD 2-byte peers.
	 *  2. non-transitive attrs: don't re-announce to ebgp peers
	 *  3. transitive known attrs: announce unmodified
	 *  4. transitive unknown attrs: set partial bit and re-announce
	 */
	for (l = 0; l < a->others_len; l++) {
		if ((oa = a->others[l]) == NULL)
			break;
		switch (oa->type) {
		case ATTR_ATOMIC_AGGREGATE:
			if ((r = attr_write(buf + wlen, len,
			    ATTR_WELL_KNOWN, ATTR_ATOMIC_AGGREGATE,
			    NULL, 0)) == -1)
				return (-1);
			break;
		case ATTR_AGGREGATOR:
			if (!rde_as4byte(peer)) {
				/* need to deflate the aggregator */
				u_int8_t	t[6];
				u_int16_t	tas;

				if ((!(oa->flags & ATTR_TRANSITIVE)) &&
				    peer->conf.ebgp) {
					r = 0;
					break;
				}

				memcpy(&tmp32, oa->data, sizeof(tmp32));
				if (ntohl(tmp32) > USHRT_MAX) {
					tas = htons(AS_TRANS);
					newaggr = oa;
				} else
					tas = htons(ntohl(tmp32));

				memcpy(t, &tas, sizeof(tas));
				memcpy(t + sizeof(tas),
				    oa->data + sizeof(tmp32),
				    oa->len - sizeof(tmp32));
				if ((r = attr_write(buf + wlen, len,
				    oa->flags, oa->type, &t, sizeof(t))) == -1)
					return (-1);
				break;
			}
			/* FALLTHROUGH */
		case ATTR_COMMUNITIES:
		case ATTR_ORIGINATOR_ID:
		case ATTR_CLUSTER_LIST:
		case ATTR_LARGE_COMMUNITIES:
			if ((!(oa->flags & ATTR_TRANSITIVE)) &&
			    peer->conf.ebgp) {
				r = 0;
				break;
			}
			if ((r = attr_write(buf + wlen, len,
			    oa->flags, oa->type, oa->data, oa->len)) == -1)
				return (-1);
			break;
		case ATTR_EXT_COMMUNITIES:
			/* handle (non-)transitive extended communities */
			if (peer->conf.ebgp) {
				ndata = community_ext_delete_non_trans(oa->data,
				    oa->len, &nlen);

				if (nlen > 0) {
					if ((r = attr_write(buf + wlen,
					    len, oa->flags, oa->type, ndata,
					    nlen)) == -1) {
						free(ndata);
						return (-1);
					}
				} else
					r = 0;
				break;
			}
			if ((r = attr_write(buf + wlen, len,
			    oa->flags, oa->type, oa->data, oa->len)) == -1)
				return (-1);
			break;
		default:
			/* unknown attribute */
			if (!(oa->flags & ATTR_TRANSITIVE)) {
				/*
				 * RFC 1771:
				 * Unrecognized non-transitive optional
				 * attributes must be quietly ignored and
				 * not passed along to other BGP peers.
				 */
				r = 0;
				break;
			}
			if ((r = attr_write(buf + wlen, len,
			    oa->flags | ATTR_PARTIAL, oa->type,
			    oa->data, oa->len)) == -1)
				return (-1);
			break;
		}
		wlen += r; len -= r;
	}

	/* NEW to OLD conversion when going sending stuff to a 2byte AS peer */
	if (neednewpath) {
		if (!peer->conf.ebgp ||
		    peer->conf.flags & PEERFLAG_TRANS_AS)
			pdata = aspath_prepend(a->aspath, peer->conf.local_as,
			    0, &plen);
		else
			pdata = aspath_prepend(a->aspath, peer->conf.local_as,
			    1, &plen);
		flags = ATTR_OPTIONAL|ATTR_TRANSITIVE;
		if (!(a->flags & F_PREFIX_ANNOUNCED))
			flags |= ATTR_PARTIAL;
		if (plen == 0)
			r = 0;
		else if ((r = attr_write(buf + wlen, len, flags,
		    ATTR_AS4_PATH, pdata, plen)) == -1)
			return (-1);
		wlen += r; len -= r;
		free(pdata);
	}
	if (newaggr) {
		flags = ATTR_OPTIONAL|ATTR_TRANSITIVE;
		if (!(a->flags & F_PREFIX_ANNOUNCED))
			flags |= ATTR_PARTIAL;
		if ((r = attr_write(buf + wlen, len, flags,
		    ATTR_AS4_AGGREGATOR, newaggr->data, newaggr->len)) == -1)
			return (-1);
		wlen += r; len -= r;
	}

	return (wlen);
}

/* minimal buffer size > withdraw len + attr len + attr hdr + afi/safi */
#define MIN_UPDATE_LEN	16

int
up_dump_prefix(u_char *buf, int len, struct prefix_queue *prefix_head,
    struct rde_peer *peer, int withdraw)
{
	struct prefix	*p;
	struct bgpd_addr addr;
	int		 r, wpos = 0;

	while ((p = TAILQ_FIRST(prefix_head)) != NULL) {
		pt_getaddr(p->re->prefix, &addr);
		if ((r = prefix_write(buf + wpos, len - wpos,
		    &addr, p->re->prefix->prefixlen, withdraw)) == -1)
			break;
		wpos += r;

		peer->up_pcnt--;
		if (withdraw) {
			prefix_destroy(p);
			peer->up_wcnt--;
			peer->prefix_sent_withdraw++;
		} else {
			/* move prefix from updates to prefixes */
			prefix_relink(p, prefix_aspath(p), 0);
			peer->up_nlricnt--;
			peer->prefix_sent_update++;
		}
	}
	return (wpos);
}

int
up_dump_attrnlri(u_char *buf, int len, struct rde_peer *peer)
{
	struct rde_aspath	*asp;
	int			 r, wpos;
	u_int16_t		 attr_len;

	/*
	 * It is possible that a queued path attribute has no nlri prefix.
	 * Ignore and remove those path attributes.
	 */
	while ((asp = TAILQ_FIRST(&peer->updates[AID_INET])) != NULL) {
		if (TAILQ_EMPTY(&asp->updates)) {
			TAILQ_REMOVE(&peer->updates[AID_INET], asp, update_l);
			asp->flags &= ~F_ATTR_UPDATE;
			peer->up_acnt--;
			/* special return for EoR markers */
			if (asp->flags & F_ATTR_EOR) {
				path_destroy(asp);
				return (-1);
			}
		} else
			break;
	}

	if (len < 2)
		fatalx("up_dump_attrnlri: buffer way too small");

	if (asp == NULL || len < MIN_UPDATE_LEN)
		goto done;
	r = up_generate_attr(buf + 2, len - 2, peer, asp, AID_INET);
	if (r == -1) {
		/*
		 * either no packet or not enough space.
		 * The length field needs to be set to zero else it would be
		 * an invalid bgp update.
		 */
done:
		bzero(buf, 2);
		return (2);
	}

	/* first dump the 2-byte path attribute length */
	attr_len = htons(r);
	memcpy(buf, &attr_len, 2);
	wpos = 2;
	/* then skip over the already dumped path attributes themselves */
	wpos += r;

	/* last but not least dump the nlri */
	r = up_dump_prefix(buf + wpos, len - wpos, &asp->updates, peer, 0);
	wpos += r;

	/* now check if all prefixes were written */
	if (TAILQ_EMPTY(&asp->updates)) {
		TAILQ_REMOVE(&peer->updates[AID_INET], asp, update_l);
		asp->flags &= ~F_ATTR_UPDATE;
		peer->up_acnt--;
	}

	return (wpos);
}

int
up_dump_mp_unreach(u_char *buf, int len, struct rde_peer *peer, u_int8_t aid)
{
	u_char		*attrbuf;
	int		 wpos, r;
	u_int16_t	 attr_len, tmp;

	if (len < MIN_UPDATE_LEN || TAILQ_EMPTY(&peer->withdraws[aid]))
		return (-1);

	/* reserve space for withdraw len, attr len */
	wpos = 2 + 2;
	attrbuf = buf + wpos;

	/* attribute header, defaulting to extended length one */
	attrbuf[0] = ATTR_OPTIONAL | ATTR_EXTLEN;
	attrbuf[1] = ATTR_MP_UNREACH_NLRI;
	wpos += 4;

	/* afi & safi */
	if (aid2afi(aid, &tmp, buf + wpos + 2))
		fatalx("up_dump_mp_unreach: bad AID");
	tmp = htons(tmp);
	memcpy(buf + wpos, &tmp, sizeof(u_int16_t));
	wpos += 3;

	r = up_dump_prefix(buf + wpos, len - wpos, &peer->withdraws[aid],
	    peer, 1);
	if (r == 0)
		return (-1);
	wpos += r;
	attr_len = r + 3;	/* prefixes + afi & safi */

	/* attribute length */
	attr_len = htons(attr_len);
	memcpy(attrbuf + 2, &attr_len, sizeof(attr_len));

	/* write length fields */
	bzero(buf, sizeof(u_int16_t));	/* withdrawn routes len */
	attr_len = htons(wpos - 4);
	memcpy(buf + 2, &attr_len, sizeof(attr_len));

	return (wpos);
}

int
up_dump_mp_reach(u_char *buf, int len, struct rde_peer *peer, u_int8_t aid)
{
	struct rde_aspath	*asp;
	int			r, wpos;
	u_int16_t		attr_len;

	/*
	 * It is possible that a queued path attribute has no nlri prefix.
	 * Ignore and remove those path attributes.
	 */
	while ((asp = TAILQ_FIRST(&peer->updates[aid])) != NULL) {
		if (TAILQ_EMPTY(&asp->updates)) {
			TAILQ_REMOVE(&peer->updates[aid], asp, update_l);
			asp->flags &= ~F_ATTR_UPDATE;
			peer->up_acnt--;
			/* special return for EoR markers */
			if (asp->flags & F_ATTR_EOR) {
				path_destroy(asp);
				return (-1);
			}
		} else
			break;
	}

	if (asp == NULL || len < MIN_UPDATE_LEN)
		return (-2);

	wpos = 4;	/* reserve space for length fields */

	/* write regular path attributes */
	r = up_generate_attr(buf + wpos, len + wpos, peer, asp, aid);
	if (r == -1)
		return (-2);
	wpos += r;

	/* write mp attribute */
	r = up_generate_mp_reach(buf + wpos, len - wpos, peer, asp, aid);
	if (r == -1)
		return (-2);
	wpos += r;

	/* write length fields */
	bzero(buf, sizeof(u_int16_t));	/* withdrawn routes len */
	attr_len = htons(wpos - 4);
	memcpy(buf + 2, &attr_len, sizeof(attr_len));

	/* now check if all prefixes were written */
	if (TAILQ_EMPTY(&asp->updates)) {
		TAILQ_REMOVE(&peer->updates[aid], asp, update_l);
		asp->flags &= ~F_ATTR_UPDATE;
		peer->up_acnt--;
	}

	return (wpos);
}
