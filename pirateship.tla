---- MODULE pirateship ----
\* This is a specification of the PirateShip consensus protocol.
\* Message delivery is assumed to be ordered and reliable
\* This spec does not model the fast path or reconfiguration
\* We also assume all txns include signatures

EXTENDS 
    Integers, 
    Sequences, 
    FiniteSets
    ,Variants
    ,Apalache

----

\* Range(f) == { f[x] : x \in DOMAIN f }
Max(S) == CHOOSE x \in S : \A y \in S : x >= y
Front(s) == SubSeq(s, 1, Len(s)-1)
Last(s) == s[Len(s)]
IsPrefix(s, t) == Len(s) <= Len(t) /\ SubSeq(s, 1, Len(s)) = SubSeq(t, 1, Len(s))

\* Set of replicas
CONSTANT
    \* @type: Set(REPLICA);
    R
\* ASSUME R # {}

\* Byzantine replicas
CONSTANT 
    \* @type: Set(REPLICA);
    BR
ASSUME BR \subseteq R

\* Set of possible transactions
CONSTANT 
    \* @type: Set(Int);
    Txs
\* ASSUME Txs # {}

\* Max number of byzantine actions
\* This parameter is completely artificial and is used to limit the state space
CONSTANT
    \* @type: Int;
    MaxByzActions
----
\* Helpers & Variable types

\* Honest replicas
HR == R \ BR

Views ==
    Nat

CONSTANT 
    \* @type: Int => REPLICA;
    Primary(_)

\* Quorum certificates are simply the index of the log entry they confirm
\* Quorum certificates do not need views as they are always formed in the current view
\* Note that in the specification, we do not model signatures anywhere. This means that signatures are omitted from the logs and messages. When modelling byzantine faults, byz replicas will not be permitted to form messages which would be discarded by honest replicas.
QCs ==
    Nat

\* Each log entry contains just a view, a txn and optionally, a quorum certificate
LogEntry == [
    view: Views, 
    tx: Txs,
    qc: SUBSET QCs]
\* A log is a sequence of log entries. The index of the log entry is its sequence number/height
\* We do not explicitly model the parent relationship, the parent of log entry i is log entry i-1
Log == Seq(LogEntry)


AppendEntries == [
    type: {"AppendEntries"},
    view: Views,
    \* In practice, it suffices to send only the log entry to append, however, for the sake of the spec, we send the entire log as we need to check that the replica has the parent of the log entry to append
    log: Log]

Votes == [
    type: {"Vote"},
    view: Views,
    \* In practice, it suffices to send only the log entry to append, however, for the sake of the spec, we send the entire log as we need to check that the replica has the parent of the log entry to append
    log: Log]

ViewChanges == [
    type: {"ViewChange"},
    view: Views,
    \* In practice, it suffices to send only the log entry to append, however, for the sake of the spec, we send the entire log as we need to check that the replica has the parent of the log entry to append
    log: Log]

\* Currently, we use separate messages for NewLeader and AppendEntries, these could be merged
NewLeaders == [
    type: {"NewLeader"},
    view: Views,
    \* In practice, it suffices to send only the log entry to append, however, for the sake of the spec, we send the entire log as we need to check that the replica has the parent of the log entry to append
    log: Log]

\* @type: $message => {type: Str, view: Int, log: $log};
AsMsg(msg) == VariantGetUnsafe("Msg", msg)

\* All possible messages
Messages == 
    AppendEntries \union 
    Votes \union 
    ViewChanges \union 
    NewLeaders

\* @typeAlias: logEntry = { view: Int, tx: Int, qc: Set(Int) };
\* @typeAlias: log = Seq($logEntry);
\*
\* @typeAlias: message = Msg({type: Str, view: Int, log: $log});
\* @typeAlias: msg = Seq($message);
typedefs == TRUE

VARIABLE
    \* messages in transit between any pair of replicas
    \* @type: REPLICA -> (REPLICA -> $msg);
    network,
    \* current view of each replica
    \* @type: REPLICA -> Int;
    view,
    \* current log of each replica
    \* @type: REPLICA -> $log;
    log,
    \* flag indicating if each replica is a primary
    \* @type: REPLICA -> Bool;
    primary,
    \* (primary only) the highest log entry on each replica replicated in this view
    \* @type: REPLICA -> (REPLICA -> Int);
    matchIndex,
    \* crash commit index of each replica
    \* @type: REPLICA -> Int;
    crashCommitIndex,
    \* byzantine commit index of each replica
    \* @type: REPLICA -> Int;
    byzCommitIndex,
    \* total number of byzantine actions taken so far by any byzantine replica
    \* @type: Int;
    byzActions

vars == <<
    network,
    view,  
    log, 
    primary, 
    matchIndex,
    crashCommitIndex,
    byzCommitIndex,
    byzActions>>


TypeOK == 
    /\ view \in [R -> Views]
    /\ log \in [R -> Log]
    \* See https://github.com/konnov/apalache-examples/blob/af6b380921b28362ac746507ab4c24741299a2f9/ben-or83/Ben_or83_inductive.tla#L64-L71
    \* /\ \A r, s \in R:
    \*     \A i \in DOMAIN network[r][s]: network[r][s][i] \in Messages
    /\ primary \in [R -> BOOLEAN]
    /\ matchIndex \in [R -> [R -> Nat]]
    /\ crashCommitIndex \in [R -> Nat]
    /\ byzCommitIndex \in [R -> Nat]
    /\ byzActions \in Nat

----
\* Initial states

\* We begin in view 0 with replica 1 as primary
Init == 
    /\ view = [r \in R |-> 0]
    /\ network = [r \in R |-> [s \in R |-> <<>>]]
    /\ log = [r \in R |-> <<>>]
    /\ primary \in { f \in [ R -> BOOLEAN ] : Cardinality({ r \in R : f[r] }) = 1 }
    /\ matchIndex = [r \in R |-> [s \in R |-> 0]]
    /\ crashCommitIndex = [r \in R |-> 0]
    /\ byzCommitIndex = [r \in R |-> 0]
    /\ byzActions = 0

Max0(S) == IF S = {} THEN 0 ELSE Max(S)

\* @type: (Int, $logEntry) => Int;
F(acc, elem) == Max(elem.qc \union {acc})

\* Given a log l, returns the index of the highest log entry with a quorum certificate, 0 if the log contains no QCs
\* type: $log => Int;
HighestQC(l) ==
    ApaFoldSeqLeft(F, 0, l)

\* TODO Called from LogChoiceRule
\* \* The view of the highest qc in log l, -1 if log contains no qcs
HighestQCView(l) == 
    IF HighestQC(l) = 0
    THEN -1
    ELSE l[HighestQC(l)].view

\* TODO Called from some actions
\* \* Given a log l, returns the index of the highest log entry with a quorum certificate over a quorum certificate
HighestQCOverQC(l) ==
    HighestQC(SubSeq(l,1,HighestQC(l)))

\* TODO Called from ReceiveEntries, ...
Max2(a,b) == IF a > b THEN a ELSE b

CONSTANT Quorums
   
\* TODO Called from SendEntries
MaxQC(p) == 
    LET \* @type: (Int, Int) => Int;
        G(acc, elem) ==
            IF \E q \in Quorums: \A n \in q: matchIndex'[p][n] >= elem THEN Max2(elem, acc) ELSE acc
        MaxQuorum ==
            ApaFoldSet(G, 0, DOMAIN log[p])
    IN IF MaxQuorum > HighestQC(log[p])
        THEN {MaxQuorum}
        ELSE {}

\* True if log l is valid log choice from the set of logs ls.
\* Assumes that l \in ls
LogChoiceRule(l,ls) ==
    \* if all logs are empty, then any l must be empty and a valid choice  
    \/ \A l2 \in ls: l2 = <<>>
    \/ /\ l # <<>>
        \* l is valid if all other logs in ls are empty (antecedent) ...
       /\ \A l2 \in ls:
            l # l2 /\ l2 # <<>> 
            =>  \* ...l is from a higher view
                \/ HighestQCView(l) > HighestQCView(l2)
                \* l is from the same view
                \/ /\ HighestQCView(l) = HighestQCView(l2)
                   /\ \/ Last(l).view > Last(l2).view
                      \/ /\ Last(l).view = Last(l2).view 
                         /\ Len(l) >= Len(l2)

\* Replica r handling AppendEntries from primary p
ReceiveEntries ==
\E r,p \in R:
    \* there must be at least one message pending
    /\ network[r][p] # <<>>
    \* and the next message is an AppendEntries
    /\ AsMsg(Head(network[r][p])).type = "AppendEntries"
    \* the replica must be in the same view
    /\ view[r] = AsMsg(Head(network[r][p])).view
    \* and must be replicating an entry from this view
    /\ Last(AsMsg(Head(network[r][p])).log).view = view[r]
    \* the replica only appends (one entry at a time) to its log
    /\ log[r] = Front(AsMsg(Head(network[r][p])).log)
    \* for convenience, we replace the replica's log with the received log but in practice we are only appending one entry
    /\ log' = [log EXCEPT ![r] =  AsMsg(Head(network[r][p])).log]
    \* we remove the AppendEntries message and reply with a Vote message.
    /\ network' = [network EXCEPT 
        ![r][p] = Tail(@),
        ![p][r] = Append(@,Variant("Msg",[
            type |-> "Vote",
            view |-> view[r],
            log |-> log'[r]
            ]))
        ]
    \* replica updates its commit indexes
    /\ crashCommitIndex' = [crashCommitIndex EXCEPT ![r] = Max2(@, HighestQC(log'[r]))]
    \* assumes that a replica can safely byz commit if there's a quorum certificate over a quorum certificate
    /\ byzCommitIndex' = [byzCommitIndex EXCEPT ![r] = Max2(@, HighestQCOverQC(log'[r]))]
    /\ UNCHANGED <<primary, view, matchIndex, byzActions>>

\* Replica r handling NewLeader from primary p
\* Note that unlike an AppendEntries message, a replica can update its view upon receiving a NewLeader message
ReceiveNewLeader ==
\E r,p \in R:
    \* there must be at least one message pending
    /\ network[r][p] # <<>>
    \* and the next message is a NewLeader
    /\ AsMsg(Head(network[r][p])).type = "NewLeader"
    \* the replica must be in the same view or lower
    /\ view[r] \leq AsMsg(Head(network[r][p])).view
    \* update the replica's local view
    \* note that we do not dispatch a view change message as a primary has already been elected
    /\ view' = [view EXCEPT ![r] = AsMsg(Head(network[r][p])).view]
    \* step down if replica was a primary
    /\ primary' = [primary EXCEPT ![r] = FALSE]
    \* reset matchIndexes, in case view was updated
    /\ matchIndex' = [matchIndex EXCEPT ![r] = [s \in R |-> 0]]
    \* the replica replaces its log with the received log
    /\ log' = [log EXCEPT ![r] =  AsMsg(Head(network[r][p])).log]
    \* we remove the NewLeader message and reply with a Vote message.
    /\ network' = [network EXCEPT 
        ![r][p] = Tail(@),
        ![p][r] = Append(@,Variant("Msg",[
            type |-> "Vote",
            view |-> view[r],
            log |-> log'[r]
            ]))
        ]
    \* replica updates its commit indexes
    \* TODO: need to allow the crash commit to decrease in the case of a byz attack
    /\ crashCommitIndex' = [crashCommitIndex EXCEPT ![r] = Max2(@,HighestQC(log'[r]))]
    /\ byzCommitIndex' = [byzCommitIndex EXCEPT ![r] = Max2(@, HighestQCOverQC(log'[r]))]
    /\ UNCHANGED <<byzActions>>

\* Primary p receiving votes from replica r
ReceiveVote ==
\E r,p \in R:
    \* p must be the primary
    /\ primary[p]
    \* and the next message is a vote from the correct view
    /\ network[p][r] # <<>>
    /\ AsMsg(Head(network[p][r])).type = "Vote"
    /\ view[p] = AsMsg(Head(network[p][r])).view
    /\ \* match index only updated if the log entry is in the current view, this means that the match index only updated in response to AppendEntries
        IF \/ AsMsg(Head(network[p][r])).log = <<>> 
           \/ Last(AsMsg(Head(network[p][r])).log).view # view[p]
        THEN UNCHANGED matchIndex
        ELSE matchIndex' = [matchIndex EXCEPT 
            ![p][r] = IF @ \leq Len(AsMsg(Head(network[p][r])).log) 
            THEN Len(AsMsg(Head(network[p][r])).log) 
            ELSE @]
    \* we remove the Vote message.
    /\ network' = [network EXCEPT ![p][r] = Tail(network[p][r])]
    /\ crashCommitIndex' = 
        [crashCommitIndex EXCEPT ![p] = 
            Max({i \in DOMAIN log[p]: \E q \in {q \in SUBSET R: Cardinality(q) >= 3}: \A n \in q: matchIndex'[p][n] >= i} \union {@})]
    /\ UNCHANGED <<view, log, primary, byzCommitIndex,byzActions>>


\* Primary p sends AppendEntries to all replicas
SendEntries ==
\E p \in R:
    \* p must be the primary
    /\ primary[p]
    /\ \E tx \in Txs:
        \* primary will not send an appendEntries to itself so update matchIndex here
        /\ matchIndex' = [matchIndex EXCEPT ![p][p] = Len(log[p]) + 1]
        \* add the new entry to the log
        /\ log' = [log EXCEPT ![p] = Append(@, [
            view |-> view[p], 
            tx |-> tx,
            qc |-> MaxQC(p)])]
        /\ network' = 
            [r \in R |-> [s \in R |->
                IF s # p \/ r=p THEN network[r][s] ELSE Append(network[r][s], Variant("Msg", [ 
                    type |-> "AppendEntries",
                    view |-> view[p],
                    log |-> log'[p]]))]]
        /\ UNCHANGED <<view, primary, crashCommitIndex, byzCommitIndex, byzActions>>

\* Replica r times out
Timeout ==
\E r \in R:
    /\ view' = [view EXCEPT ![r] = view[r] + 1]
    \* send a view change message to the new primary (even if it's itself)
    /\ network' = [network EXCEPT ![Primary(view'[r])][r] = Append(@, Variant("Msg", [ 
        type |-> "ViewChange",
        view |-> view'[r],
        log |-> log[r]]))
        ]
    \* step down if replica was a primary
    /\ primary' = [primary EXCEPT ![r] = FALSE]
    \* reset matchIndexes, these are not used until the node is elected primary
    /\ matchIndex' = [matchIndex EXCEPT ![r] = [s \in R |-> 0]]
    /\ UNCHANGED <<log, crashCommitIndex, byzCommitIndex, byzActions>>

\* Replica r becomes primary
BecomePrimary ==
\E r \in R:
    \* replica must be assigned the new view
    /\ r = Primary(view[r])
    \* a byz quorum must have voted for the replica. 
    /\ \E q \in {q \in SUBSET R: Cardinality(q) >= 3}:
        \* A byz quorum has voted if there is a ViewChange message at r from all quorum members for the current view.
        /\ \A n \in q: 
            /\ network[r][n] # <<>>
            /\ AsMsg(Head(network[r][n])).type = "ViewChange"
            /\ view[r] = AsMsg(Head(network[r][n])).view
        \* r nondeterministically picks a log from the logs in the set of ViewChange messages s.t. 
        /\ \E l1 \in {AsMsg(Head(network[r][n])).log : n \in q}:
                LogChoiceRule(l1, {AsMsg(Head(network[r][n])).log : n \in q})
            /\ log' = [log EXCEPT ![r] = log[r]]
        \* Need to update network to remove the view change message and send a NewLeader message to all replicas
        /\ network' = [r1 \in R |-> [r2 \in R |-> 
            IF r1 = r /\ r2 \in q 
            THEN Tail(network[r1][r2]) 
            ELSE IF r1 # r /\ r2 = r 
                THEN Append(network[r1][r2], Variant("Msg",[ 
                    type |-> "NewLeader",
                    view |-> view[r],
                    log |-> log'[r]]))
                ELSE network[r1][r2]]]
    \* replica becomes a primary
    /\ primary' = [primary EXCEPT ![r] = TRUE]
    \* primary updates its commit indexes
    \* TODO: need to allow the crash commit to decrease in the case of a byz attack
    /\ crashCommitIndex' = [crashCommitIndex EXCEPT ![r] = Max2(@,HighestQC(log'[r]))]
    /\ byzCommitIndex' = [byzCommitIndex EXCEPT ![r] = Max2(@, HighestQCOverQC(log'[r]))]
    /\ UNCHANGED <<view, matchIndex, byzActions>>

\* Replicas will discard messages from previous views or extra view changes messages
\* Note that replicas must always discard messages as the pairwise channels are ordered so a replica may need to discard an out-of-date message to process a more recent one
DiscardMessage ==
\E r,s \in R:
    \* We can safely discard any message from views lower than the current view because
    \* r's view is monotonically increasing and all actions ignore messages from lower views.
    LET selected == SelectSeq(network[r][s], LAMBDA m: AsMsg(m).view >= view[r]) IN
    /\ network' = 
        [network EXCEPT ![r][s] =
            \* However, we must keep all but the first ViewChange messages because a pending NewLeader
            \* message may make r abdicate its primary status, causing later ViewChange messages
            \* to have relevance. Discarding the first ViewChange message is safe because TLC
            \* will explore all possible behaviors, i.e., it will explore the behavior where the
            \* first ViewChange message is kept and r times out, and the behavior where the first
            \* ViewChange message is discarded and r times out.
            \* Assuming r is primary, we could also safely discard all ViewChange message with a view
            \* equal to r's view because if r steps down, it will increment its view.
            IF primary[r] /\ AsMsg(Head(selected)).type = "ViewChange"
            THEN Tail(selected)
            ELSE selected]
    /\ UNCHANGED <<view, log, primary, matchIndex, crashCommitIndex, byzCommitIndex, byzActions>>

----
\* Byzantine actions
\* Byzantine actions can only be taken by byzantine replicas (BR) and if there are byzantine actions left to take

\* A byzantine replica might vote for an entry without actually appending it to its log.
\* This byzantine action currently has the same preconditions as AppendEntries
ByzOmitEntries ==
\E p,r \in R:
    /\ r \in BR
    /\ byzActions < MaxByzActions
    /\ byzActions' = byzActions + 1
    \* there must be at least one message pending
    /\ network[r][p] # <<>>
    \* and the next message is an AppendEntries
    /\ AsMsg(Head(network[r][p])).type = "AppendEntries"
    \* the replica must be in the same view
    /\ view[r] = AsMsg(Head(network[r][p])).view
    \* the replica only appends one entry to its log
    /\ log[r] = Front(AsMsg(Head(network[r][p])).log)
    \* we remove the AppendEntries message and reply with a Vote message.
    /\ network' = [network EXCEPT 
        ![r][p] = Tail(@),
        ![p][r] = Append(@,Variant("Msg",[
            type |-> "Vote",
            view |-> view[r],
            log |-> AsMsg(Head(network[r][p])).log
            ]))
        ]
    /\ UNCHANGED <<primary, view, matchIndex, crashCommitIndex, byzCommitIndex, log>>

\* We allow a byzantine primary to equivocate by changing the txn in an AppendEntries message
ByzPrimaryEquivocate ==
\E p,r \in R:
    /\ p \in BR
    /\ byzActions < MaxByzActions
    /\ byzActions' = byzActions + 1
    /\ network[r][p] # <<>>
    /\ LET m == AsMsg(Head(network[r][p])) IN
       /\ m.type = "AppendEntries"
       /\ m.log # <<>>
       /\ \E t \in Txs:
               network' = [ network EXCEPT
                ![r][p][1] = 
                   Variant("Msg", [ 
                       type |-> "AppendEntries",
                       view |-> m.view,
                       log |-> SubSeq(m.log,1,Len(m.log)-1) \o <<[Last(m.log) EXCEPT !.tx = 1]>>
                       ])
                   ]
    /\ UNCHANGED <<view, log, primary, matchIndex, crashCommitIndex, byzCommitIndex>>

Next ==
    \/ SendEntries
    \/ Timeout
    \/ BecomePrimary
    \/ ReceiveEntries
    \/ ReceiveVote
    \/ ReceiveNewLeader
    \/ ByzOmitEntries
    \/ ByzPrimaryEquivocate
    \/ DiscardMessage
    
====
\* Next state relation
\* Note that the byzantine actions are included here but can be disabled by setting MaxByzActions to 0 or BR to {}.
NextOff == 
    \E r \in R: 
        \/ SendEntries(r)
        \/ Timeout(r)
        \/ BecomePrimary(r)
        \/ \E s \in R: 
            \/ ReceiveEntries(r,s)
            \/ ReceiveVote(r,s)
            \/ ReceiveNewLeader(r,s)
            \/ ByzOmitEntries(r,s)
            \/ ByzPrimaryEquivocate(r,s)
            \/ DiscardMessage(r,s)

Fairness ==
    \* Only Timeout if there is no primary.
    /\ \A r \in HR: WF_vars(\A i \in DOMAIN primary: TRUE # primary[i] /\ Timeout(r))
    /\ \A r \in HR: WF_vars(BecomePrimary(r))
    /\ \A r,s \in HR: WF_vars(DiscardMessage(r,s))
    /\ \A r \in HR: WF_vars(SendEntries(r))
    /\ \A r,s \in HR: WF_vars(ReceiveEntries(r,s))
    /\ \A r,s \in HR: WF_vars(ReceiveVote(r,s))
    /\ \A r,s \in HR: WF_vars(ReceiveNewLeader(r,s))
    \* Omit any byzantine actions from the fairness condition.

Spec == 
    /\ Init
    /\ [][Next]_vars
    /\ Fairness

----
\* Properties

\* Correct replicas are either honest or byzantine when no byzantine actions have been taken yet
CR == IF byzActions = 0 THEN R ELSE HR

Committed(r) ==
    IF crashCommitIndex[r] = 0
    THEN << >>
    ELSE SubSeq(log[r], 1, crashCommitIndex[r])

\* If no byzantine actions have been taken, then the committed logs of all replicas must be prefixes of each other
\* This, together with CommittedLogAppendOnlyProp, is the classic CFT safety property
\* Note that if any nodes have been byzantine, then this property is not guaranteed to hold on any node
\* LogInv implies that the byzantine committed logs of replicas are prefixes too, as IndexBoundsInv ensures that the byzCommitIndex is always less than or equal to the crashCommitIndex.
LogInv ==
    byzActions = 0 =>
        \A i, j \in R :
            \/ IsPrefix(Committed(i),Committed(j)) 
            \/ IsPrefix(Committed(j),Committed(i))

ByzCommitted(r) ==
    IF byzCommitIndex[r] = 0
    THEN << >>
    ELSE SubSeq(log[r], 1, byzCommitIndex[r])

\* Variant of LogInv for the byzantine commit index and correct replicas only
\* We make no assertions about the state of byzantine replicas
ByzLogInv ==
    \A i, j \in CR :
        \/ IsPrefix(ByzCommitted(i),ByzCommitted(j)) 
        \/ IsPrefix(ByzCommitted(j),ByzCommitted(i))

\* If no byzantine actions have been taken, then each replica only appends to its committed log
CommittedLogAppendOnlyProp ==
    [][byzActions = 0 => \A i \in R :
        IsPrefix(Committed(i), Committed(i)')]_vars

\* Each correct replica only appends to its byzantine committed log
ByzCommittedLogAppendOnlyProp ==
    [][\A i \in CR :
        IsPrefix(ByzCommitted(i), ByzCommitted(i)')]_vars

MaxView ==
    LET V == { view[i] : i \in DOMAIN view } IN CHOOSE n \in V: \A v \in V: v <= n

\* At most one correct replica is primary in a view
OneLeaderPerTermInv ==
    \A v \in 0..MaxView, r \in CR :
        view[r] = v /\ primary[r] 
        => \A s \in R \ {r} : view[s] = v => ~primary[s]


IndexBoundsInv ==
    \A r \in CR :
        /\ crashCommitIndex[r] <= Len(log[r])
        /\ byzCommitIndex[r] <= crashCommitIndex[r]

WellFormedLogInv ==
    \A r \in CR :
        \A i, j \in DOMAIN log[r] :
            i < j => log[r][i].view <= log[r][j].view

WellFormedQCsInv ==
    \A r \in CR : 
        \A i \in DOMAIN log[r] : 
            \A q \in log[r][i].qc :
                \* qcs are always for previous entries
                /\ q < i
                \* qcs are always formed in the current view 
                /\ log[r][q].view = log[r][i].view
                \* qcs are in increasing order
                /\ \A j \in 1..i-1 : 
                    \A qj \in log[r][j].qc: qj < q
====