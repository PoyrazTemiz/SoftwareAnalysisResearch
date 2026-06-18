---- MODULE pBFT ----
EXTENDS Naturals, FiniteSets

CONSTANT N \* number of total replicas, including the primary
CONSTANT F \* maximum number of faulty replicas
CONSTANT Clients
CONSTANT Ops
CONSTANT Timestamps
CONSTANT Views
CONSTANT MaxSeq

ASSUME N = 3 * F + 1

Replicas == 0..(N-1)
SeqNums == 1..MaxSeq

VARIABLES 
    pState, \* The state of the primary
    rState, \* The state of the replica
    msgs \* The set of messages in the system

\* May need a different digest as if there are multiple clinets, the timestamp night be the same :/
\* It might be necessary to change the timestamp from a simple constant set into a variable that get's assigned
\* an incremented value because I think now the timestamps can be random and not ordered
\* also same timestamp can be used which causes an issue

RequestMsg == [type: {"REQUEST"}, o: Ops, t: Timestamps, c: Clients]
PrePrepareMsg == [type: {"PRE-PREPARE"}, v: Views, n: SeqNums, d: Timestamps, m: RequestMsg, p: Replicas]
PrepareMsg == [type: {"PREPARE"}, v: Views, n: SeqNums, d: Timestamps, i: Replicas]
CommitMsg == [type: {"COMMIT"}, v: Views, n: SeqNums, d: Timestamps, i: Replicas]
ReplyMsg == [type: {"REPLY"}, v: Views, t: Timestamps, c: Clients, i: Replicas, r: Ops]

Messages == RequestMsg \cup PrePrepareMsg \cup PrepareMsg \cup CommitMsg \cup ReplyMsg

Digest(m) == m.t

PrimaryOf(v) == v % N

IsReplica(i, v) == i # PrimaryOf(v)

PBTypeOK ==
    /\ pState \in [v: Views, nextN: 1..(MaxSeq+1)]
    /\ rState \in [Replicas -> [v: Views,
                                h: Nat,
                                H: Nat,
                                log: SUBSET Messages,
                                lastExec: 0..MaxSeq]]
    /\ msgs \subseteq Messages

PBInit ==
    /\ msgs = {}
    /\ pState = [v |-> CHOOSE v \in Views: TRUE,
                 nextN |-> 1]
    /\ rState = [i \in Replicas |-> [v |-> pState.v,
                                     h |-> 0, 
                                     H |-> MaxSeq + 1, 
                                     log |-> {},
                                     lastExec |-> 0]]

ClientAccepts(c, t, r) ==
  \E S \in SUBSET Replicas:
    /\ Cardinality(S) >= F + 1
    /\ \A i \in S:
          \E reply \in msgs:
            /\ reply.type = "REPLY"
            /\ reply.c = c
            /\ reply.t = t
            /\ reply.r = r
            /\ reply.i = i

ClientHasOutstandingRequest(c) ==
  \E m \in msgs:
    /\ m.type = "REQUEST"
    /\ m.c = c
    /\ ~ClientAccepts(m.c, m.t, m.o)

RequestAlreadyAssigned(m) ==
  \E pp \in msgs:
    /\ pp.type = "PRE-PREPARE"
    /\ pp.m.c = m.c
    /\ pp.m.t = m.t

ClientRequest(c, o, t) ==
    /\ c \in Clients
    /\ o \in Ops
    /\ t \in Timestamps
    /\ ~ClientHasOutstandingRequest(c)
    /\ LET req == [type |-> "REQUEST", o |-> o, t |-> t, c |-> c] IN
       /\ req \notin msgs
       /\ msgs' = msgs \cup {req}
    /\ UNCHANGED <<pState, rState>>

\* PrimaryPrePrepareFor(m) maybe parameterize this?
PrimaryPrePrepare ==
    \E m \in msgs:
        /\ m.type = "REQUEST"
        /\ pState.nextN \in SeqNums
        /\ ~RequestAlreadyAssigned(m)
        /\ LET v == pState.v
               n == pState.nextN
               d == Digest(m)
               prePrepareMsg == [type |-> "PRE-PREPARE",
                                 v |-> v,
                                 n |-> n,
                                 d |-> d,
                                 m |-> m,
                                 p |-> PrimaryOf(v)]
            IN
                /\ msgs' = msgs \cup {prePrepareMsg}
                /\ pState' = [pState EXCEPT !.nextN = n + 1]
                /\ UNCHANGED rState

ReplicaRcvPrePrepare(i) ==
  \E m \in msgs:
    /\ m.type = "PRE-PREPARE"
    /\ m.p = PrimaryOf(m.v)
    /\ m \notin rState[i].log
    /\ rState[i].v = m.v
    /\ rState[i].h < m.n
    /\ m.n < rState[i].H
    /\ \A pp2 \in rState[i].log:
         ~(pp2.type = "PRE-PREPARE" /\ pp2.v = m.v /\ pp2.n = m.n /\ pp2.d # m.d)
    /\ rState' = [rState EXCEPT ![i].log = rState[i].log \cup {m}]
    /\ UNCHANGED <<msgs, pState>>


ReplicaSendPrepare(i) ==
  \E m \in rState[i].log:
    /\ m.type = "PRE-PREPARE"
    /\ rState[i].v = m.v
    /\ IsReplica(i, m.v)
    /\ LET prepareMsg == [type |-> "PREPARE",
                          v |-> m.v,
                          n |-> m.n,
                          d |-> m.d,
                          i |-> i]
       IN
          /\ prepareMsg \notin msgs
          /\ msgs' = msgs \cup {prepareMsg}
          /\ rState' = [rState EXCEPT ![i].log = rState[i].log \cup {prepareMsg}]
          /\ UNCHANGED pState

ReplicaRcvPrepare(i) ==
  \E m \in msgs:
    /\ m.type = "PREPARE"
    /\ rState[i].v = m.v
    /\ rState[i].h < m.n
    /\ m.n < rState[i].H
    /\ m \notin rState[i].log
    /\ rState' = [rState EXCEPT ![i].log = rState[i].log \cup {m}]
    /\ UNCHANGED <<msgs, pState>>

Prepared(i, v, n, d) ==
  /\ \E pp \in rState[i].log:
        /\ pp.type = "PRE-PREPARE"
        /\ pp.v = v
        /\ pp.n = n
        /\ pp.d = d
  /\ Cardinality({p \in rState[i].log:
        /\ p.type = "PREPARE"
        /\ p.v = v
        /\ p.n = n
        /\ p.d = d
        /\ IsReplica(p.i, v)}) >= 2 * F


ReplicaSendCommit(i) ==
  \E v \in Views:
  \E n \in SeqNums:
  \E d \in Timestamps:
    /\ Prepared(i, v, n, d)
    /\ LET commitMsg == [type |-> "COMMIT",
                         v |-> v,
                         n |-> n,
                         d |-> d,
                         i |-> i]
       IN
          /\ commitMsg \notin msgs
          /\ msgs' = msgs \cup {commitMsg}
          /\ rState' = [rState EXCEPT ![i].log = rState[i].log \cup {commitMsg}]
          /\ UNCHANGED pState

ReplicaRcvCommit(i) ==
  \E m \in msgs:
    /\ m.type = "COMMIT"
    /\ rState[i].v = m.v
    /\ rState[i].h < m.n
    /\ m.n < rState[i].H
    /\ m \notin rState[i].log
    /\ rState' = [rState EXCEPT ![i].log = rState[i].log \cup {m}]
    /\ UNCHANGED <<msgs, pState>>

CommittedLocal(i, v, n, d) ==
  /\ Prepared(i, v, n, d)
  /\ Cardinality({c \in rState[i].log:
        /\ c.type = "COMMIT"
        /\ c.v = v
        /\ c.n = n
        /\ c.d = d}) >= 2 * F + 1


ReplicaSendReply(i) ==
  \E pp \in rState[i].log:
    /\ pp.type = "PRE-PREPARE"
    /\ pp.n = rState[i].lastExec + 1
    /\ CommittedLocal(i, pp.v, pp.n, pp.d)
    /\ LET replyMsg == [type |-> "REPLY",
                        v |-> pp.v,
                        t |-> pp.m.t,
                        c |-> pp.m.c,
                        i |-> i,
                        r |-> pp.m.o]
       IN
          /\ replyMsg \notin msgs
          /\ msgs' = msgs \cup {replyMsg}
          /\ rState' = [rState EXCEPT ![i].lastExec = pp.n]
          /\ UNCHANGED pState




PBNext ==
  \/ \E c \in Clients, o \in Ops, t \in Timestamps:
        ClientRequest(c, o, t)
  \/ PrimaryPrePrepare
  \/ \E i \in Replicas:
        ReplicaRcvPrePrepare(i)
  \/ \E i \in Replicas:
        ReplicaSendPrepare(i)
  \/ \E i \in Replicas:
        ReplicaRcvPrepare(i)
  \/ \E i \in Replicas:
        ReplicaSendCommit(i)
  \/ \E i \in Replicas:
        ReplicaRcvCommit(i)
  \/ \E i \in Replicas:
        ReplicaSendReply(i)

RequestSent(c, o, t) ==
  [type |-> "REQUEST", o |-> o, t |-> t, c |-> c] \in msgs

GoodWeatherSuccess ==
  \A c \in Clients, o \in Ops, t \in Timestamps:
    [](RequestSent(c, o, t) => <>ClientAccepts(c, t, o))

vars == <<pState, rState, msgs>>

PBSpec ==
  PBInit
  /\ [][PBNext]_vars
  /\ WF_vars(PrimaryPrePrepare)
  /\ \A i \in Replicas:
       /\ WF_vars(ReplicaRcvPrePrepare(i))
       /\ WF_vars(ReplicaSendPrepare(i))
       /\ WF_vars(ReplicaRcvPrepare(i))
       /\ WF_vars(ReplicaSendCommit(i))
       /\ WF_vars(ReplicaRcvCommit(i))
       /\ WF_vars(ReplicaSendReply(i))

NoConflictingPrePrepare ==
  \A pp1, pp2 \in msgs:
    /\ pp1.type = "PRE-PREPARE"
    /\ pp2.type = "PRE-PREPARE"
    /\ pp1.v = pp2.v
    /\ pp1.n = pp2.n
    => pp1.m = pp2.m

====
