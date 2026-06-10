---- MODULE pBFT ----
EXTENDS Naturals

CONSTANT N \* number of total replicas, including the primary
CONSTANT F \* maximum number of faulty replicas
CONSTANT Clients
CONSTANT Ops
CONSTANT Views
CONSTANT MaxSeq

ASSUME N = 3 * F + 1

Replicas == 0..(N-1)
SeqNums == 1..MaxSeq

VARIABLES 
    pState, \* The state of the primary
    rState, \* The state of the replica
    msgs \* The set of messages in the system
====

RequestMsg == [type: {"REQUEST"}, o: Ops, t: Nat, c: Clients]
PrePrepareMsg == [type: {"PRE-PREPARE"}, v: Views, n: SeqNums, d: Nat, m: RequestMsg, p: Replicas]
PrepareMsg == [type: {"PREPARE"}, v: Views, n: SeqNums, d: Nat, i: Replicas]
CommitMsg == [type: {"COMMIT"}, v: Views, n: SeqNums, d: Nat, i: Replicas]
ReplyMsg == [type: {"REPLY"}, v: Views, t: Nat, c: Clients, i: Replicas, r: Ops]

Messages == RequestMsg \cup PrePrepareMsg \cup PrepareMsg \cup CommitMsg \cup ReplyMsg

Digest(m) == m.t

PBTypeOK ==
    /\ pState \in [v: Views, primary: Replicas, nextN: 1..(MaxSeq+1)]
    /\ rState \in [Replicas -> [v: Views, h: Nat, H: Nat, log: SUBSET Messages]]
    /\ msgs \subseteq Messages

PBInit ==
    /\ msgs = {}
    /\ pState = [v |-> CHOOSE v \in Views: TRUE, primary |-> 0, nextN |-> 1]
    /\ rState = [i \in Replicas |-> [v |-> pState.v,
                                     h |-> 0, 
                                     H |-> MaxSeq + 1, 
                                     log |-> {}]]

PBNext ==
  \/ \E c \in Clients, o \in Ops, t \in Nat:
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


ClientRequest(c, o, t) ==
    /\ c \in Clients
    /\ o \in Ops
    /\ t \in Nat
    /\ LET req == [type |-> "REQUEST", o |-> o, t |-> t, c |-> c] IN
       msgs' = msgs \cup {req}
    /\ UNCHANGED <<pState, rState>>


PrimaryPrePrepare ==
    \E m \in msgs:
        /\ m.type = "REQUEST"
        /\ pState.nextN \in SeqNums
        /\ LET v == pState.v IN
               n == pState.nextN
               d == Digest(m)
               prePrepareMsg == [type |-> "PRE-PREPARE",
                                    v |-> v,
                                    n |-> n,
                                    d |-> d,
                                    m |-> m,
                                    p |-> pState.primary]
            IN
                /\ msgs' = msgs \cup {prePrepareMsg}
                /\ pState' = [pState EXCEPT !.nextN = n + 1]
                /\ UNCHANGED rState

ReplicaRcvPrePrepare(i) ==
  \E m \in msgs:
    /\ m.type = "PRE-PREPARE"
    /\ rState[i].v = m.v
    /\ rState[i].h < m.n
    /\ m.n < rState[i].H
    /\ \A pp2 \in rState[i].log:
         ~(pp2.type = "PRE-PREPARE" /\ pp2.v = m.v /\ pp2.n = m.n /\ pp2.d # m.d)
    /\ rState' = [rState EXCEPT ![i].log = @ \cup {m}]
    /\ UNCHANGED <<msgs, pState>>


ReplicaSendPrepare(i) ==
  \E m \in rState[i].log:
    /\ m.type = "PRE-PREPARE"
    /\ rState[i].v = m.v
    /\ LET prepareMsg == [type |-> "PREPARE",
                          v |-> m.v,
                          n |-> m.n,
                          d |-> m.d,
                          i |-> i]
       IN
          /\ prepareMsg \notin msgs
          /\ msgs' = msgs \cup {prepareMsg}
          /\ rState' = [rState EXCEPT ![i].log = @ \cup {prepareMsg}]
          /\ UNCHANGED pState

ReplicaRcvPrepare(i) ==
  \E m \in msgs:
    /\ m.type = "PREPARE"
    /\ rState[i].v = m.v
    /\ rState[i].h < m.n
    /\ m.n < rState[i].H
    /\ m \notin rState[i].log
    /\ rState' = [rState EXCEPT ![i].log = @ \cup {m}]
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
        /\ p.d = d}) >= 2 * F


ReplicaSendCommit(i) ==
  \E v \in Views:
  \E n \in SeqNums:
  \E d \in Nat:
    /\ Prepared(i, v, n, d)
    /\ LET commitMsg == [type |-> "COMMIT",
                         v |-> v,
                         n |-> n,
                         d |-> d,
                         i |-> i]
       IN
          /\ commitMsg \notin msgs
          /\ msgs' = msgs \cup {commitMsg}
          /\ UNCHANGED <<pState, rState>>

ReplicaRcvCommit(i) ==
  \E m \in msgs:
    /\ m.type = "COMMIT"
    /\ rState[i].v = m.v
    /\ rState[i].h < m.n
    /\ m.n < rState[i].H
    /\ m \notin rState[i].log
    /\ rState' = [rState EXCEPT ![i].log = @ \cup {m}]
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
          /\ UNCHANGED <<pState, rState>>

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



\* I think we still have to model if a non primary recevies request. In that case, 
\* the request needs to be sent to primary from the replica
\* + we don't check for signature I don't know if we should tho
\* The committed systemwide predicate described in the model is not modeled but I don't know where it would fit exactly
\* How do you wanna model actions being executed, or is sending a reply enough for modeling this