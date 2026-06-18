---- MODULE pBFT ----
EXTENDS Naturals, FiniteSets

CONSTANT N \* number of total replicas, including the primary
CONSTANT F \* maximum number of faulty replicas
CONSTANT Clients
CONSTANT Ops
CONSTANT Timestamps
CONSTANT Views
CONSTANT MaxSeq
CONSTANT StateDigests
CONSTANT WindowSize

ASSUME N >= 3 * F + 1

Replicas == 0..(N-1)
SeqNums == 1..MaxSeq
CheckpointNums == 0..MaxSeq

VARIABLES 
    pState, \* The state of the primary
    rState, \* The state of the replica
    msgs \* The set of messages in the system

RequestMsg == [type: {"REQUEST"}, o: Ops, t: Timestamps, c: Clients]
PrePrepareMsg == [type: {"PRE-PREPARE"}, v: Views, n: SeqNums, d: Timestamps, m: RequestMsg, p: Replicas]
PrepareMsg == [type: {"PREPARE"}, v: Views, n: SeqNums, d: Timestamps, i: Replicas]
CommitMsg == [type: {"COMMIT"}, v: Views, n: SeqNums, d: Timestamps, i: Replicas]
ReplyMsg == [type: {"REPLY"}, v: Views, t: Timestamps, c: Clients, i: Replicas, r: Ops]
CheckpointMsg == [type: {"CHECKPOINT"}, n: CheckpointNums, d: StateDigests, i: Replicas]

ProtocolMsg ==
  PrePrepareMsg \cup PrepareMsg \cup CommitMsg

ViewChangeMsg ==
  [type: {"VIEW-CHANGE"},
   v: Views,
   i: Replicas,   
   checkpointN: CheckpointNums,
   checkpointD: StateDigests,
   prepared: SUBSET PrePrepareMsg]

NewViewMsg == [type: {"NEW-VIEW"}, v: Views, i: Replicas, viewChanges: SUBSET ViewChangeMsg, prePrepares: SUBSET PrePrepareMsg]

Messages == RequestMsg \cup PrePrepareMsg \cup PrepareMsg \cup CommitMsg \cup ReplyMsg \cup CheckpointMsg \cup ViewChangeMsg \cup NewViewMsg

Digest(m) == m.t

PrimaryOf(v) == v % N

IsReplica(i, v) == i # PrimaryOf(v)

TimestampAlreadyUsed(t) ==
  \E m \in msgs:
    /\ m.type = "REQUEST"
    /\ m.t = t

AllEarlierTimestampsUsed(t) ==
  \A t2 \in Timestamps:
    t2 < t => TimestampAlreadyUsed(t2)

ViewChangesFor(v) ==
  {m \in msgs:
    /\ m.type = "VIEW-CHANGE"
    /\ m.v = v}

NewViewExists(v) ==
  \E nv \in msgs:
    /\ nv.type = "NEW-VIEW"
    /\ nv.v = v

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

ReplicaWaiting(i) ==
  \E req \in msgs:
    /\ req.type = "REQUEST"
    /\ ~ClientAccepts(req.c, req.t, req.o)

CanStartViewChange(i) ==
  /\ ReplicaWaiting(i)
  /\ pState.nextN = MaxSeq + 1

ClientHasOutstandingRequest(c) ==
  \E m \in msgs:
    /\ m.type = "REQUEST"
    /\ m.c = c
    /\ ~ClientAccepts(m.c, m.t, m.o)

RequestAlreadyAssignedInView(m, v) ==
  \E pp \in msgs:
    /\ pp.type = "PRE-PREPARE"
    /\ pp.v = v
    /\ pp.m.c = m.c
    /\ pp.m.t = m.t

ClientRequest(c, o, t) ==
    /\ c \in Clients
    /\ o \in Ops
    /\ t \in Timestamps
    /\ ~ClientHasOutstandingRequest(c)
    /\ ~TimestampAlreadyUsed(t)
    /\ AllEarlierTimestampsUsed(t)
    /\ LET req == [type |-> "REQUEST", o |-> o, t |-> t, c |-> c] IN
       msgs' = msgs \cup {req}
    /\ UNCHANGED <<pState, rState>>

PrimaryPrePrepare ==
    \E m \in msgs:
        /\ m.type = "REQUEST"
        /\ pState.nextN \in SeqNums
        /\ ~RequestAlreadyAssignedInView(m, pState.v)
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

IsCheckpointSeq(n) == n > 0

StateDigest(i, n) == CHOOSE d \in StateDigests: TRUE

MessageSeq(m) ==
  IF m.type \in {"PRE-PREPARE", "PREPARE", "COMMIT", "CHECKPOINT"}
  THEN m.n
  ELSE 0

StableCheckpoint(n, d) ==
  Cardinality({cp \in msgs:
    /\ cp.type = "CHECKPOINT"
    /\ cp.n = n
    /\ cp.d = d}) >= 2 * F + 1

PrePreparesInLog(i) ==
  {m \in rState[i].log: m.type = "PRE-PREPARE"}

PreparedPrePrepares(i) ==
  {pp \in PrePreparesInLog(i):
    /\ pp.n > rState[i].h
    /\ Prepared(i, pp.v, pp.n, pp.d)}
      
ReplicaSendCheckpoint(i) ==
  /\ IsCheckpointSeq(rState[i].lastExec)
  /\ LET cp == [type |-> "CHECKPOINT",
                n |-> rState[i].lastExec,
                d |-> StateDigest(i, rState[i].lastExec),
                i |-> i]
     IN
        /\ cp \notin msgs
        /\ msgs' = msgs \cup {cp}
        /\ UNCHANGED <<pState, rState>>

ReplicaStabilizeCheckpoint(i) ==
  \E n \in 0..MaxSeq:
  \E d \in StateDigests:
    /\ n > rState[i].h
    /\ StableCheckpoint(n, d)
    /\ rState' =
         [rState EXCEPT
            ![i].h = n,
            ![i].H = n + WindowSize,
            ![i].log = {m \in rState[i].log:
                          MessageSeq(m) > n}]
    /\ UNCHANGED <<msgs, pState>>

ReplicaSendViewChange(i) ==
  \E newV \in Views:
    /\ newV = rState[i].v + 1
    /\ ~NewViewExists(newV)
    /\ CanStartViewChange(i)
    /\ LET vc == [type |-> "VIEW-CHANGE",
                  v |-> newV,
                  i |-> i,
                  checkpointN |-> rState[i].h,
                  checkpointD |-> StateDigest(i, rState[i].h),
                  prepared |-> PreparedPrePrepares(i)]
       IN
          /\ vc \notin msgs
          /\ msgs' = msgs \cup {vc}
          /\ rState' = [rState EXCEPT ![i].v = newV]
          /\ UNCHANGED pState

ViewChangeQuorum(v, VCs) ==
  /\ VCs \subseteq msgs
  /\ Cardinality(VCs) >= 2 * F + 1
  /\ \A vc \in VCs:
       /\ vc.type = "VIEW-CHANGE"
       /\ vc.v = v

NewViewCheckpointN(nv) ==
  CHOOSE n \in CheckpointNums:
    /\ \E vc \in nv.viewChanges:
         vc.checkpointN = n
    /\ \A vc \in nv.viewChanges:
         vc.checkpointN <= n

NewViewIsSafe(nv) ==
  /\ ViewChangeQuorum(nv.v, nv.viewChanges)
  /\ \A pp \in nv.prePrepares:
       /\ pp.v = nv.v
       /\ pp.n > NewViewCheckpointN(nv)

SafePrePrepares(v, VCs) ==
  UNION {
    { [type |-> "PRE-PREPARE",
       v |-> v,
       n |-> pp.n,
       d |-> pp.d,
       m |-> pp.m,
       p |-> PrimaryOf(v)] :
        pp \in {x \in vc.prepared :
                  /\ x.type = "PRE-PREPARE"
                  /\ x.n > vc.checkpointN} }
    : vc \in VCs
  }

NextPrimarySeq(nv) ==
  CHOOSE n \in 1..(MaxSeq + 1):
    /\ n > NewViewCheckpointN(nv)
    /\ \A pp \in nv.prePrepares: pp.n < n
    /\ \/ n = NewViewCheckpointN(nv) + 1
       \/ \E pp \in nv.prePrepares: pp.n = n - 1

PrimarySendNewView ==
  \E v \in Views:
    /\ ~NewViewExists(v)
    /\ Cardinality(ViewChangesFor(v)) >= 2 * F + 1
    /\ LET VCs == ViewChangesFor(v)
           nv == [type |-> "NEW-VIEW",
                  v |-> v,
                  i |-> PrimaryOf(v),
                  viewChanges |-> VCs,
                  prePrepares |-> SafePrePrepares(v, VCs)]
       IN
          /\ nv \notin msgs
          /\ msgs' = msgs \cup {nv}
          /\ pState' = [v |-> v, nextN |-> NextPrimarySeq(nv)]
          /\ UNCHANGED rState

ReplicaRcvNewView(i) ==
  \E nv \in msgs:
    /\ nv.type = "NEW-VIEW"
    /\ nv.v >= rState[i].v
    /\ nv.i = PrimaryOf(nv.v)
    /\ NewViewIsSafe(nv)
    /\ rState' =
         [rState EXCEPT
            ![i].v = nv.v,
            ![i].h = NewViewCheckpointN(nv),
            ![i].H = NewViewCheckpointN(nv) + WindowSize,
            ![i].log = rState[i].log \cup nv.prePrepares]
    /\ UNCHANGED <<msgs, pState>>

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
  \/ \E i \in Replicas:
        ReplicaSendCheckpoint(i)
  \/ \E i \in Replicas:
        ReplicaStabilizeCheckpoint(i)
  \/ \E i \in Replicas:
        ReplicaSendViewChange(i)
  \/ PrimarySendNewView
  \/ \E i \in Replicas:
        ReplicaRcvNewView(i)


RequestSent(c, o, t) ==
  [type |-> "REQUEST", o |-> o, t |-> t, c |-> c] \in msgs

RequestSuccess ==
  \A c \in Clients, o \in Ops, t \in Timestamps:
    [](RequestSent(c, o, t) => <>ClientAccepts(c, t, o))

vars == <<pState, rState, msgs>>

PBSpec ==
  PBInit
  /\ [][PBNext]_vars
  /\ WF_vars(PrimaryPrePrepare)
  /\ WF_vars(PrimarySendNewView)
  /\ \A i \in Replicas:
       /\ WF_vars(ReplicaRcvPrePrepare(i))
       /\ WF_vars(ReplicaSendPrepare(i))
       /\ WF_vars(ReplicaRcvPrepare(i))
       /\ WF_vars(ReplicaSendCommit(i))
       /\ WF_vars(ReplicaRcvCommit(i))
       /\ WF_vars(ReplicaSendReply(i))
       /\ WF_vars(ReplicaSendCheckpoint(i))
       /\ WF_vars(ReplicaStabilizeCheckpoint(i))
       /\ WF_vars(ReplicaSendViewChange(i))
       /\ WF_vars(ReplicaRcvNewView(i))

NoConflictingPrePrepare ==
  \A pp1, pp2 \in msgs:
    /\ pp1.type = "PRE-PREPARE"
    /\ pp2.type = "PRE-PREPARE"
    /\ pp1.v = pp2.v
    /\ pp1.n = pp2.n
    => pp1.m = pp2.m

NoConflictingStableCheckpoints ==
  \A n \in 0..MaxSeq:
  \A d1, d2 \in StateDigests:
    /\ StableCheckpoint(n, d1)
    /\ StableCheckpoint(n, d2)
    => d1 = d2

NoConflictingCommittedAcrossViews ==
  \A i, j \in Replicas:
  \A v1, v2 \in Views:
  \A n \in SeqNums:
  \A d1, d2 \in Timestamps:
    /\ CommittedLocal(i, v1, n, d1)
    /\ CommittedLocal(j, v2, n, d2)
    => d1 = d2

NewViewOnlyAboveCheckpoint ==
  \A nv \in msgs:
    nv.type = "NEW-VIEW" =>
      \A pp \in nv.prePrepares:
        pp.n > NewViewCheckpointN(nv)

====
