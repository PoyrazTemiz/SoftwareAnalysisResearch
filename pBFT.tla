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

Messages == RequestMsg \cup PrePrepareMsg \cup PrepareMsg

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