---- MODULE pirateship ----
\* This is a specification of the PirateShip consensus protocol.
\* Message delivery is assumed to be ordered and reliable
\* This spec does not model the fast path or reconfiguration
\* We also assume all txns include signatures

EXTENDS 
    Naturals, 
    Sequences, 
    FiniteSets, 
    FiniteSetsExt, 
    SequencesExt

VARIABLE
    \* messages in transit between any pair of replicas
    network,
    \* current view of each replica
    view,
    \* current log of each replica
    log,
    \* flag indicating if each replica is primary
    primary,
    \* (primary only) the highest log entry on each replica replicated in this view
    matchIndex,
    \* crash commit index of each replica
    crashCommitIndex,
    \* byzantine commit index of each replica
    byzCommitIndex,
    \* total number of byzantine actions taken so far
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

----
\* Model parameters

\* Set of replicas
R == 1..4

\* Byzantine replicas
BR == {4}

\* Set of quourms for crash fault tolerance
CQ == {q \in SUBSET R: Cardinality(q) >= 3}

\* Set of quourms for byzantine fault tolerance
BQ == {q \in SUBSET R: Cardinality(q) >= 3}

\* Limit on Views
Views == 0..3

\* Set of possible transactions
Txs == 1..2

\* Max number of byzantine actions
\* This parameter is completely artificial and is used to limit the state space
MaxByzActions == 2

----
\* Variable types

\* Number of replicas
N == Cardinality(R)

\* Honest replicas
HR == R \ BR

\* Quorum certificates are simply the index of the log entry they confirm
\* We will likely need to add view information to this
\* Note that in the specification, we do not model signatures anywhere. This means that signatures are omitted from the logs and messages, when modelling byzantine faults, byz replicas will not be permitted to form messages which would be discarded by honest replicas.
QCs == Nat

\* Each log entry contains just a view, a txn and optionally, a quorum certificate
LogEntry == [
    view: Views, 
    tx: Txs,
    \* For convenience, we represent a quorum certificate as a set but it can only be empty or a singleton
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
    \* As with AppendEntries, we send the entire log for the sake of the spec
    log: Log]

ViewChanges == [
    type: {"ViewChange"},
    view: Views,
    log: Log]
        
NewLeaders == [
    type: {"NewLeader"},
    view: Views,
    log: Log]

\* All possible messages
Messages == 
    AppendEntries \union 
    Votes \union 
    ViewChanges \union 
    NewLeaders

TypeOK == 
    /\ view \in [R -> Views]
    /\ log \in [R -> Log]
    /\ \A r, s \in R:
        \A i \in DOMAIN network[r][s]: network[r][s][i] \in Messages
    /\ primary \in [R -> BOOLEAN]
    /\ matchIndex \in [R -> [R -> Nat]]
    /\ crashCommitIndex \in [R -> Nat]
    /\ byzCommitIndex \in [R -> Nat]
    /\ byzActions \in Nat

----
\* Initial states

Init == 
    /\ view = [r \in R |-> 0]
    /\ network = [r \in R |-> [s \in R |-> <<>>]]
    /\ log = [r \in R |-> <<>>]
    /\ primary = [r \in R |-> r = 1]
    /\ matchIndex = [r \in R |-> [s \in R |-> 0]]
    /\ crashCommitIndex = [r \in R |-> 0]
    /\ byzCommitIndex = [r \in R |-> 0]
    /\ byzActions = 0

----
\* Actions

Extract(S) == CHOOSE x : x \in S

\* Given a log l, returns the index of the highest log entry with a quorum certificate
HighestQC(l) ==
    IF UNION {l[i].qc : i \in DOMAIN l} = {}
    THEN 0
    ELSE Max(UNION  {l[i].qc : i \in DOMAIN l})

\* Given a log l, returns the index of the highest log entry with a quorum certificate over a quorum certificate
HighestQCOverQC(l) ==
    IF HighestQC(l) = 0
    THEN 0
    ELSE HighestQC(SubSeq(l,1,HighestQC(l)))

Max2(a,b) == IF a > b THEN a ELSE b

\* Replica r handling AppendEntries from primary p
ReceiveEntries(r, p) ==
    \* there must be at least one message pending
    /\ network[r][p] # <<>>
    \* and the next message is an AppendEntries
    /\ Head(network[r][p]).type = "AppendEntries"
    \* the replica must be in the same view
    /\ view[r] = Head(network[r][p]).view
    \* and must be replicating an entry from this view
    /\ Last(Head(network[r][p]).log).view = view[r]
    \* the replica only appends (one entry at a time) to its log
    /\ log[r] = Front(Head(network[r][p]).log)
    \* for convenience, we replace the replica's log with the received log but in practice we are only appending one entry
    /\ log' = [log EXCEPT ![r] =  Head(network[r][p]).log]
    \* we remove the message and reply with a vote
    /\ network' = [network EXCEPT 
        ![r][p] = Tail(@),
        ![p][r] = Append(@,[
            type |-> "Vote",
            view |-> view[r],
            log |-> log'[r]
            ])
        ]
    \* replica updates is commit indexes
    /\ crashCommitIndex' = [crashCommitIndex EXCEPT ![r] = Max2(@, HighestQC(log'[r]))]
    \* assumes that a replica can safely byz commit if there's a quorum certificate over a quorum certificate
    /\ byzCommitIndex' = [byzCommitIndex EXCEPT ![r] = Max2(@, HighestQCOverQC(log'[r]))]
    /\ UNCHANGED <<primary, view, matchIndex, byzActions>>

\* Replica r handling NewLeader from primary p
ReceiveNewLeader(r, p) ==
    \* there must be at least one message pending
    /\ network[r][p] # <<>>
    \* and the next message is an NewLeader
    /\ Head(network[r][p]).type = "NewLeader"
    \* the replica must be in the same view
    /\ view[r] = Head(network[r][p]).view
    \* the replica replaces its log with the received log
    /\ log' = [log EXCEPT ![r] =  Head(network[r][p]).log]
    \* we message and reply with a vote
    /\ network' = [network EXCEPT 
        ![r][p] = Tail(@),
        ![p][r] = Append(@,[
            type |-> "Vote",
            view |-> view[r],
            log |-> log'[r]
            ])
        ]
    \* replica updates is commit indexes
    /\ crashCommitIndex' = [crashCommitIndex EXCEPT ![r] = Max2(@, HighestQC(log'[r]))]
    /\ byzCommitIndex' = [byzCommitIndex EXCEPT ![r] = Max2(@, HighestQCOverQC(log'[r]))]
    /\ UNCHANGED <<primary, view, matchIndex,byzActions>>

\* Primary p receiving votes from replica r
ReceiveVote(p, r) ==
    \* p must be the primary
    /\ primary[p]
    \* and the next message is a vote from the correct view
    /\ network[p][r] # <<>>
    /\ Head(network[p][r]).type = "Vote"
    /\ view[r] = Head(network[p][r]).view
    /\ \* match index only updated if the log entry is in the current view, this means that the match index only updated in response to AppendEntries
        IF \/ Head(network[p][r]).log = <<>> 
           \/ Last(Head(network[p][r]).log).view # view[r]
        THEN UNCHANGED matchIndex
        ELSE matchIndex' = [matchIndex EXCEPT 
            ![p][r] = IF @ \leq Len(Head(network[p][r]).log) 
            THEN Len(Head(network[p][r]).log) 
            ELSE @]
    /\ network' = [network EXCEPT ![p][r] = Tail(network[p][r])]
    /\ crashCommitIndex' = 
        [crashCommitIndex EXCEPT ![p] = 
            Max({i \in DOMAIN log[p]: \E q \in CQ: \A n \in q: matchIndex'[p][n] >= i} \union {@})]
    /\ UNCHANGED <<view, log, primary, byzCommitIndex,byzActions>>

\* Like Max but returns a set
MaxSet(S) == IF S = {} THEN {} ELSE {Max(S)}
Max0(S) == IF S = {} THEN 0 ELSE Max(S)

MaxQC(p) == 
    LET MaxQuorum == 
        Max0({i \in DOMAIN log[p]: \E q \in BQ: \A n \in q: matchIndex'[p][n] >= i})
    IN IF MaxQuorum > Max0(UNION {log[p][i].qc : i \in DOMAIN log[p]})
        THEN {MaxQuorum}
        ELSE {}

\* Primary p sends AppendEntries to all replicas
SendEntries(p) ==
    /\ primary[p]
    /\ \E tx \in Txs:
        /\ \A i \in DOMAIN log[p]: log[p][i].tx # tx
        /\ matchIndex' = [matchIndex EXCEPT ![p][p] = Len(log[p]) + 1]
        /\ log' = [log EXCEPT ![p] = Append(@, [
            view |-> view[p], 
            tx |-> tx,
            qc |-> MaxQC(p)])]
        /\ network' = 
            [r \in R |-> [s \in R |->
                IF s # p \/ r=p THEN network[r][s] ELSE Append(network[r][s], [ 
                    type |-> "AppendEntries",
                    view |-> view[p],
                    log |-> log'[p]])]]
        /\ UNCHANGED <<view, primary, crashCommitIndex, byzCommitIndex, byzActions>>

\* Replica r times out
Timeout(r) ==
    /\ view[r] + 1 \in Views
    /\ view' = [view EXCEPT ![r] = view[r] + 1]
    /\ network' = [network EXCEPT ![(view'[r] % N) + 1][r] = Append(@, [ 
        type |-> "ViewChange",
        view |-> view'[r],
        log |-> log[r]])
        ]
    /\ primary' = [primary EXCEPT ![r] = FALSE]
    /\ matchIndex' = [matchIndex EXCEPT ![r] = [s \in R |-> 0]]
    /\ UNCHANGED <<log, crashCommitIndex, byzCommitIndex, byzActions>>


\* True if l is valid log choice from ls
LogChoiceRule(l,ls) == 
    /\ \/ \A l2 \in ls: l2 = <<>>
       \/ /\ l # <<>>
          /\ \A l2 \in ls:
                l # l2 /\ l2 # <<>> 
                =>  \/ Last(l).view > Last(l2).view
                    \/  /\ Last(l).view = Last(l2).view 
                        /\ Len(l) >= Len(l2)

\* Replica r becomes primary
BecomePrimary(r) ==
    /\ r = (view[r] % N) + 1
    /\ \E q \in BQ:
        /\ \A n \in q: 
            /\ network[r][n] # <<>>
            /\ Head(network[r][n]).type = "ViewChange"
            /\ view[r] = Head(network[r][n]).view
        /\ \E l1 \in {Head(network[r][n]).log : n \in q}:
            LogChoiceRule(l1, {Head(network[r][n]).log : n \in q})
            /\ log' = [log EXCEPT ![r] = l1]
        /\ network' = [r1 \in R |-> [r2 \in R |-> 
            IF r1 = r /\ r2 \in q 
            THEN Tail(network[r1][r2]) 
            ELSE IF r1 # r /\ r2 = r 
                THEN Append(network[r1][r2], [ 
                    type |-> "NewLeader",
                    view |-> view[r],
                    log |-> log'[r]])
                ELSE network[r1][r2]]]
    /\ primary' = [primary EXCEPT ![r] = TRUE]
    /\ UNCHANGED <<view, matchIndex, crashCommitIndex, byzCommitIndex, byzActions>>

\* Replicas will discard messages from previous views
DiscardMessage(r) ==
    /\ \E n \in R:
        /\ network[r][n] # <<>>
        /\ \/ Head(network[r][n]).view < view[r]
           \/ Head(network[r][n]).type = "ViewChange" /\ primary[r]
        /\ network' = [network EXCEPT ![r][n] = Tail(@)]
    /\ UNCHANGED <<view, log, primary, matchIndex, crashCommitIndex, byzCommitIndex, byzActions>>

----
\* Byzantine actions
\* Byzantine actions can only be taken by byzantine replicas (BR) and if there are byzantine actions left to take

\* A byzantine replica might vote for an entry without actually appending it to its log.
\* This byzantine action currently has the same preconditions as AppendEntries
ByzOmitEntries(r, p) ==
    /\ r \in BR
    /\ byzActions < MaxByzActions
    /\ byzActions' = byzActions + 1
    \* there must be at least one message pending
    /\ network[r][p] # <<>>
    \* and the next message is an AppendEntries
    /\ Head(network[r][p]).type = "AppendEntries"
    \* the replica must be in the same view
    /\ view[r] = Head(network[r][p]).view
    \* the replica only appends one entry to its log
    /\ log[r] = Front(Head(network[r][p]).log)
    \* we message and reply with a vote
    /\ network' = [network EXCEPT 
        ![r][p] = Tail(@),
        ![p][r] = Append(@,[
            type |-> "Vote",
            view |-> view[r],
            log |-> Head(network[r][p]).log
            ])
        ]
    /\ UNCHANGED <<primary, view, matchIndex, crashCommitIndex, byzCommitIndex, log>>

\* Given an append entries message, returns the same message with the txn changed to 1
ModifyAppendEntries(m) == [
    type |-> "AppendEntries",
    view |-> m.view,
    log |-> SubSeq(m.log,1,Len(m.log)-1) \o 
        <<[Last(m.log) EXCEPT !.tx = 1]>>
]


\* We allow a byzantine primary to equivocate by changing the txn in an AppendEntries message
ByzPrimaryEquivocate(p) ==
    /\ p \in BR
    /\ byzActions < MaxByzActions
    /\ byzActions' = byzActions + 1
    /\ \E r \in R:
        /\ network[r][p] # <<>>
        /\ Head(network[r][p]).type = "AppendEntries"
        /\ Head(network[r][p]).log # <<>>
        /\ network' = [network EXCEPT 
            ![r][p][1] = ModifyAppendEntries(@)]
    /\ UNCHANGED <<view, log, primary, matchIndex, crashCommitIndex, byzCommitIndex>>

\* Next state relation
\* Note that the byzantine actions are included here but can be disabled by setting MaxByzActions to 0 or BR to {}.
Next == 
    \E r \in R: 
        \/ SendEntries(r)
        \/ Timeout(r)
        \/ DiscardMessage(r)
        \/ BecomePrimary(r)
        \/ ByzPrimaryEquivocate(r)
        \/ \E s \in R: 
            \/ ReceiveEntries(r,s)
            \/ ReceiveVote(r,s)
            \/ ReceiveNewLeader(r,s)
            \/ ByzOmitEntries(r,s)

Spec == 
    /\ Init
    /\ [][Next]_vars
    \* Only Timeout if there is no primary.
    /\ \A r \in HR: WF_vars(TRUE \notin Range(primary) /\ Timeout(r))
    /\ \A r \in HR: WF_vars(BecomePrimary(r))
    /\ \A r \in HR: WF_vars(DiscardMessage(r))
    /\ \A r \in HR: WF_vars(SendEntries(r))
    /\ \A r,s \in HR: WF_vars(ReceiveEntries(r,s))
    /\ \A r,s \in HR: WF_vars(ReceiveVote(r,s))
    /\ \A r,s \in HR: WF_vars(ReceiveNewLeader(r,s))
    \* Omit any byzantine actions from the fairness condition.

----
\* Properties

Committed(r) ==
    IF crashCommitIndex[r] = 0
    THEN << >>
    ELSE SubSeq(log[r], 1, crashCommitIndex[r])

\* If no byzantine actions have been taken, then the committed logs of all replicas must be prefixes of each other
\* This, together with CommittedLogAppendOnlyProp, is the classic CFT safety property
LogInv ==
    byzActions = 0 =>
        \A i, j \in R :
            \/ IsPrefix(Committed(i),Committed(j)) 
            \/ IsPrefix(Committed(j),Committed(i))

ByzCommitted(r) ==
    IF byzCommitIndex[r] = 0
    THEN << >>
    ELSE SubSeq(log[r], 1, byzCommitIndex[r])

ByzLogInv ==
    \A i, j \in HR :
        \/ IsPrefix(ByzCommitted(i),ByzCommitted(j)) 
        \/ IsPrefix(ByzCommitted(j),ByzCommitted(i))

CommittedLogAppendOnlyProp ==
    [][\A i \in R :
        IsPrefix(Committed(i), Committed(i)')]_vars

CrashCommitIndexMonotonic ==
    [][\A r \in HR :
            crashCommitIndex'[r] >= crashCommitIndex[r]]_vars

ByzCommitIndexMonotonic ==
    [][\A r \in HR :
            byzCommitIndex'[r] >= byzCommitIndex[r]]_vars

OneLeaderPerTermInv ==
    \A v \in Views, r \in HR :
        view[r] = v /\ primary[r] 
        => \A s \in R \ {r} : view[s] = v => ~primary[s]

RepeatedlyCrashCommitProgressProp ==
    []<><<\A r \in HR : crashCommitIndex[r]' > crashCommitIndex[r]>>_crashCommitIndex

RepeatedlyByzCommitProgressProp ==
    []<><<\A r \in HR : byzCommitIndex[r]' > byzCommitIndex[r]>>_byzCommitIndex

RepeatedlyLeaderProp ==
    []<>(TRUE \in Range(primary))

AllMessagesConsumedProp ==
    []<>(\A r, s \in R : network[r][s] = <<>>)

IndexBoundsInv ==
    \A r \in HR :
        /\ crashCommitIndex[r] <= Len(log[r])
        /\ byzCommitIndex[r] <= crashCommitIndex[r]

WellFormedLogInv ==
    \A r \in HR :
        \A i, j \in DOMAIN log[r] :
            i < j => log[r][i].view <= log[r][j].view

WellFormedQCsInv ==
    \A r \in HR : 
        \A i \in DOMAIN log[r] : 
            \A q \in log[r][i].qc :
                \* qcs are always for previous entries
                /\ q < i
                \* qcs are always formed in the current view 
                /\ log[r][q].view = log[r][i].view
                \* qcs are in increasing order
                /\ \A j \in 1..i-1 : 
                    \A qj \in log[r][j].qc: qj < q

----

\* Add a few monitors/canaries to check if interesting states are reachable.

Monitors == INSTANCE TLCMonitor WITH TLCMonitorMagicNumber <- 0

CrashCommitIndexAt1 ==
   Monitors!TLCMonitor(\A r \in HR: crashCommitIndex[r] = 1, "CrashCommitIndex@1")

CrashCommitIndexAt2 ==
   Monitors!TLCMonitor(\A r \in HR: crashCommitIndex[r] = 2, "CrashCommitIndex@2")

ByzCommitIndexAt1 ==
   Monitors!TLCMonitor(\A r \in HR: byzCommitIndex[r] = 1, "ByzCommitIndex@1")

ByzCommitIndexAt2 ==
   Monitors!TLCMonitor(\A r \in HR: byzCommitIndex[r] = 2, "ByzCommitIndex@2")

MonitorPostcondition ==
    Monitors!TLCCheckMonitors

PrintMonitors ==
    Monitors!TLCPrintMonitors
====