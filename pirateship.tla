---- MODULE pirateship ----
\* This is a specification of the PirateShip consensus protocol.
\* Message delivery is assumed to be ordered and reliable
\* This spec does not model the fast path or reconfiguration
\* We also assume all txns are signed

EXTENDS 
    Integers, 
    Sequences, 
    FiniteSets, 
    FiniteSetsExt, 
    SequencesExt

----
\* Constants

\* Set of replicas
CONSTANT R
ASSUME R # {}

\* Byzantine replicas
CONSTANT BR
ASSUME BR \subseteq R /\ Cardinality(R) >= 3*Cardinality(BR) + 1

\* Set of possible transactions
CONSTANT Txs
ASSUME Txs # {}

\* Max number of byzantine actions
\* This parameter is completely artificial and is used to limit the state space
CONSTANT MaxByzActions

----
\* Variables

VARIABLE
    \* messages in transit between any pair of replicas
    network,
    \* current view of each replica
    view,
    \* current log of each replica
    log,
    \* flag indicating if each replica is a primary
    primary,
    \* (primary only) the highest log entry on each replica replicated in this view
    prepareQC,
    \* crash commit index of each replica
    crashCommitIndex,
    \* byzantine commit index of each replica
    byzCommitIndex,
    \* total number of byzantine actions taken so far by any byzantine replica
    byzActions,
    \* (primary only) flag indicating if the primary has stabilized the view
    viewStable

vars == <<
    network,
    view,  
    log, 
    primary, 
    prepareQC,
    crashCommitIndex,
    byzCommitIndex,
    byzActions,
    viewStable>>

----
\* Helpers & Variable types

\* Number of replicas
N == Cardinality(R)

\* Set of quorums for crash fault tolerance (simple majority).
CQ == {q \in SUBSET R: Cardinality(q) >= N - ((N-1) \div 2)}

\* Set of quorums for byzantine fault tolerance (supermajority).
BQ == {q \in SUBSET R: Cardinality(q) >= N - ((N-1) \div 3)}

\* Honest replicas
HR == R \ BR

Views ==  Nat

ReplicaSeq ==
    CHOOSE s \in [ 1..N -> R ]: Range(s) = R

Primary(v) ==
    ReplicaSeq[(v % N) + 1]

\* Quorum certificates (QCs) are simply the index of the log entry they confirm
\* Quorum certificates do not need views as they are always formed in the current view
\* Note that in the specification, we do not model signatures anywhere. This means that signatures are omitted from the logs and messages. When modelling byzantine faults, byz replicas will not be permitted to form messages which would be discarded by honest replicas.
QC == Nat

\* Each log entry contains a view, a txn and optionally, quorum certificates for crash and byzantine faults
LogEntry == [
    view: Views, 
    tx: Seq(Txs),
    \* For convenience, we represent a quorum certificate as a set but it can only be empty or a singleton
    byzQC: SUBSET QC,
    crashQC: SUBSET QC]

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

\* Currently, we use separate messages for NewView and AppendEntries, these could be merged
NewViews == [
    type: {"NewView"},
    view: Views,
    log: Log]

\* All possible messages
Messages == 
    AppendEntries \union 
    Votes \union 
    ViewChanges \union 
    NewViews

TypeOK == 
    /\ view \in [R -> Views]
    /\ log \in [R -> Log]
    /\ \A r, s \in R:
        \A i \in DOMAIN network[r][s]: network[r][s][i] \in Messages
    /\ primary \in [R -> BOOLEAN]
    /\ prepareQC \in [R -> [R -> Nat]]
    /\ crashCommitIndex \in [R -> Nat]
    /\ byzCommitIndex \in [R -> Nat]
    /\ byzActions \in Nat

----
\* Initial states

\* We begin in view 0 with a non-deterministically chosen replica as primary.
Init == 
    \* Compare src/consensus/handler.rs#ConsensusState
    /\ view = [r \in R |-> 0]
    /\ network = [r \in R |-> [s \in R |-> <<>>]]
    /\ log = [r \in R |-> <<>>]
    /\ primary \in { f \in [ R -> BOOLEAN ] : Cardinality({ r \in R : f[r] }) = 1 }
    /\ prepareQC = [r \in R |-> [s \in R |-> 0]]
    /\ crashCommitIndex = [r \in R |-> 0]
    /\ byzCommitIndex = [r \in R |-> 0]
    /\ byzActions = 0
    /\ viewStable = primary

----
\* Actions

IsByzQC(e) ==
    e.byzQC # {}

IsCrashQC(e) ==
    e.crashQC # {}

\* Given a log l, returns the index of the highest log entry with a crashQC, 0 if the log contains no crashQCs
HighestCrashQC(l) ==
    LET idx == SelectLastInSeq(l, IsCrashQC)
    IN IF idx = 0 THEN 0 ELSE Max(l[idx].crashQC)

\* Given a log l, returns the index of the highest log entry with a byzQC, 0 if the log contains no byzQCs
HighestByzQC(l) ==
    LET idx == SelectLastInSeq(l, IsByzQC)
    IN IF idx = 0 THEN 0 ELSE Max(l[idx].byzQC)

\* Given a log l, returns the index of the highest log entry with a byzQC over a byzQC
HighestQCOverQC(l) ==
    LET lidx == HighestByzQC(l)
        idx == SelectLastInSubSeq(l, 1, lidx, IsByzQC)
    IN IF idx = 0 THEN 0 ELSE Max(l[idx].byzQC)

Max2(a,b) == IF a > b THEN a ELSE b
Min2(a,b) == IF a < b THEN a ELSE b

MaxQuorum(Q, l, m, default) == 
    LET RECURSIVE RMaxQuorum(_)
        RMaxQuorum(i) ==
            IF i = default THEN default
            ELSE IF \E q \in Q: \A n \in q: m[n] >= i
                 THEN i ELSE RMaxQuorum(i-1)
    IN RMaxQuorum(Len(l))

\* Checks if a log l is well formed e.g. views are monotonically increasing
WellFormedLog(l) ==
    \A i \in DOMAIN l :
        \* check views are monotonically increasing
        /\ i > 1 => l[i-1].view <= l[i].view
        \* check byzQCs are well formed
        /\ \A q \in l[i].byzQC :
            \* byzQCs are always for previous entries
            /\ q < i
            \* byzQCs are always formed in the current view 
            /\ l[q].view = l[i].view
            \* byzQCs are in increasing order
            /\ \A j \in 1..i-1 : 
                \A qj \in l[j].byzQC: qj < q
        \* check crashQCs are well formed
        /\ \A q \in l[i].crashQC :
            \* crashQCs are always for previous entries
            /\ q < i
            \* crashQCs are in increasing order
            /\ \A j \in 1..i-1 : 
                \A qj \in l[j].crashQC: qj < q

\* Replica r handling AppendEntries from primary p
\* Compare: src/consensus/steady_state.rs#do_append_entries
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
    \* received log must be well formed
    /\ WellFormedLog(Head(network[r][p]).log)
    \* for convenience, we replace the replica's log with the received log but in practice we are only appending one entry
    /\ log' = [log EXCEPT ![r] =  Head(network[r][p]).log]
    \* we remove the AppendEntries message and reply with a Vote message.
    /\ network' = [network EXCEPT 
        ![r][p] = Tail(@),
        ![p][r] = Append(@,[
            type |-> "Vote",
            view |-> view[r],
            log |-> log'[r]
            ])
        ]
    \* replica updates its crash commit index provided the new commit index is greater than the current one
    \* the only time a crash commit index can decrease is on the receipt of a NewView message if there's been a byz attack
    /\ crashCommitIndex' = [crashCommitIndex EXCEPT ![r] = Max2(@, HighestCrashQC(log'[r]))]
    \* assumes that a replica can safely byz commit if there's a quorum certificate over a quorum certificate
    /\ byzCommitIndex' = [byzCommitIndex EXCEPT ![r] = Max2(@, HighestQCOverQC(log'[r]))]
    /\ UNCHANGED <<primary, view, prepareQC, byzActions, viewStable>>

\* Replica r handling NewView from primary p
\* Note that unlike an AppendEntries message, a replica can update its view upon receiving a NewView message
ReceiveNewView(r, p) ==
    \* there must be at least one message pending
    /\ network[r][p] # <<>>
    \* and the next message is a NewView
    /\ Head(network[r][p]).type = "NewView"
    \* the replica must be in the same view or lower
    /\ view[r] \leq Head(network[r][p]).view
    \* received log must be well formed
    /\ WellFormedLog(Head(network[r][p]).log)
    \* update the replica's local view
    \* note that we do not dispatch a view change message as a primary has already been elected
    /\ view' = [view EXCEPT ![r] = Head(network[r][p]).view]
    \* step down if replica was a primary
    /\ primary' = [primary EXCEPT ![r] = FALSE]
    /\ viewStable' = [viewStable EXCEPT ![r] = FALSE]
    \* reset prepareQCs, in case view was updated
    /\ prepareQC' = [prepareQC EXCEPT ![r] = [s \in R |-> 0]]
    \* the replica replaces its log with the received log
    /\ log' = [log EXCEPT ![r] =  Head(network[r][p]).log]
    \* we remove the NewView message and reply with a Vote message.
    /\ network' = [network EXCEPT 
        ![r][p] = Tail(@),
        ![p][r] = Append(@,[
            type |-> "Vote",
            view |-> view[r],
            log |-> log'[r]
            ])
        ]
    \* replica must update its crash commit index
    \* Crash commit index may be decreased if there's been an byz attack
    /\ crashCommitIndex' = [crashCommitIndex EXCEPT ![r] = Min2(@, Len(log'[r]))]
    /\ UNCHANGED <<byzActions, byzCommitIndex>>

\* True iff primary p is in a stable view
\* A view is stable when a byzantine quorum have the view's first log entry
CheckViewStability(p) ==
    LET inView(e) == e.view=view[p] IN
    \E Q \in BQ: 
        \A q \in Q: 
            prepareQC'[p][q] >= SelectInSeq(log[p], inView)

\* Primary p receiving votes from replica r
\* Compare: src/consensus/steady_state.rs#do_process_vote
ReceiveVote(p, r) ==
    \* p must be the primary
    /\ primary[p]
    \* and the next message is a vote from the correct view
    /\ network[p][r] # <<>>
    /\ Head(network[p][r]).type = "Vote"
    /\ view[p] = Head(network[p][r]).view
    /\ prepareQC' = [prepareQC EXCEPT 
        ![p][r] = IF @ \leq Len(Head(network[p][r]).log) 
        THEN Len(Head(network[p][r]).log) 
        ELSE @]
    \* we remove the Vote message.
    /\ network' = [network EXCEPT ![p][r] = Tail(network[p][r])]
    \* if view is not already stable, check if it is now
    /\ viewStable' = [viewStable EXCEPT ![p] = 
            IF @ THEN @ ELSE CheckViewStability(p)]
    \* If view is stable, then the primary can update its commit indexes
    /\ IF viewStable'[p] THEN 
            /\ crashCommitIndex' = [crashCommitIndex EXCEPT ![p] = 
                MaxQuorum(CQ, log[p], prepareQC'[p], @)]
            /\ byzCommitIndex' = [byzCommitIndex EXCEPT ![p] = 
                HighestByzQC(SubSeq(log[p],1,MaxQuorum(BQ, log[p], prepareQC'[p], 0)))]
        ELSE UNCHANGED <<crashCommitIndex, byzCommitIndex>>
    /\ UNCHANGED <<view, log, primary, byzActions>>

MaxCrashQC(l,p) ==
    IF crashCommitIndex[p] > HighestCrashQC(l)
    THEN {crashCommitIndex[p]}
    ELSE {}

MaxByzQC(l, m) == 
    IF MaxQuorum(BQ, l, m, 0) > HighestByzQC(l)
    THEN {MaxQuorum(BQ, l, m, 0)}
    ELSE {}

\* Primary p sends AppendEntries to all replicas
\* Compare: src/consensus/steady_state.rs#do_append_entries
SendEntries(p) ==
    \* p must be the primary
    /\ primary[p]
    \* and view must be stable
    /\ viewStable[p]
    /\ \E tx \in Txs:
        \* primary will not send an appendEntries to itself so update prepareQC here
        /\ prepareQC' = [prepareQC EXCEPT ![p][p] = Len(log[p]) + 1]
        \* add the new entry to the log
        /\ log' = [log EXCEPT ![p] = Append(@, [
            view |-> view[p],
            \* for simplicity, each txn batch includes a single txn
            tx |-> <<tx>>,
            crashQC |-> MaxCrashQC(log[p], p),
            byzQC |-> MaxByzQC(log[p], prepareQC'[p])])]
        /\ network' = 
            [r \in R |-> [s \in R |->
                IF s # p \/ r=p THEN network[r][s] ELSE Append(network[r][s], [ 
                    type |-> "AppendEntries",
                    view |-> view[p],
                    log |-> log'[p]])]]
        /\ UNCHANGED <<view, primary, crashCommitIndex, byzCommitIndex, byzActions, viewStable>>

\* Replica r times out
\* Compare: src/consensus/view_change.rs#do_init_view_change
Timeout(r) ==
    /\ view' = [view EXCEPT ![r] = view[r] + 1]
    \* send a view change message to the new primary (even if it's itself)
    /\ network' = [network EXCEPT ![Primary(view'[r])][r] = Append(@, [ 
        type |-> "ViewChange",
        view |-> view'[r],
        log |-> log[r]])
        ]
    \* step down if replica was a primary
    /\ primary' = [primary EXCEPT ![r] = FALSE]
    /\ viewStable' = [viewStable EXCEPT ![r] = FALSE]
    \* reset prepareQCs, these are not used until the node is elected primary
    /\ prepareQC' = [prepareQC EXCEPT ![r] = [s \in R |-> 0]]
    /\ UNCHANGED <<log, crashCommitIndex, byzCommitIndex, byzActions>>

\* The view of the highest byzQC in log l, -1 if log contains no qcs
HighestQCView(l) == 
    LET idx == HighestByzQC(l) IN
    IF idx = 0 THEN -1 ELSE l[idx].view

\* True if log l is valid log choice from the set of logs ls.
\* Assumes that l \in ls
\* Compare: src/consensus/view_change.rs#fork_choice_rule_get
LogChoiceRule(l,ls) ==
    \* if all logs are empty, then any l must be empty and a valid choice  
    \/ \A l2 \in ls: l2 = <<>>
    \/ /\ l # <<>>
        \* l is valid if all other logs in ls are empty or l is from a higher view or 
       /\ LET v1 == HighestQCView(l)                     
          IN \A l2 \in ls:
                \* l is valid if all other logs in ls are empty or...
                l # l2 /\ l2 # <<>> 
                =>  LET v2 == HighestQCView(l2) IN
                    \* l is from a higher view or...
                    \/ v1 > v2
                    \* l is from the same view but at least as long
                    \/ /\ v1 = v2
                       /\ \/ Last(l).view > Last(l2).view
                          \/ /\ Last(l).view = Last(l2).view 
                             /\ Len(l) >= Len(l2)

\* Replica r becomes primary
\* Compare: src/consensus/view_change.rs#do_init_new_leader
BecomePrimary(r) ==
    \* replica must be assigned the new view
    /\ r = Primary(view[r])
    \* a byz quorum must have voted for the replica
    /\ \E q \in BQ:
        /\ \A n \in q: 
            /\ network[r][n] # <<>>
            /\ Head(network[r][n]).type = "ViewChange"
            /\ view[r] = Head(network[r][n]).view
        /\ \E l1 \in {Head(network[r][n]).log : n \in q}:
            \* Non-deterministically pick a log from the set of logs in the quorum that satisfy the log choice rule.
            /\ LogChoiceRule(l1, {Head(network[r][n]).log : n \in q})
            \* Primary adopts chosen log and adds a new entry in the new view
            /\ log' = [log EXCEPT ![r] = Append(l1, [
                view |-> view[r],
                tx |-> <<>>,
                crashQC |-> {},
                byzQC |-> {}])]
            /\ prepareQC' = [prepareQC EXCEPT ![r][r] = Len(log'[r])]
        \* Need to update network to remove the view change message and send a NewView message to all replicas
        /\ network' = [r1 \in R |-> [r2 \in R |-> 
            IF r1 = r /\ r2 \in q 
            THEN Tail(network[r1][r2]) 
            ELSE IF r1 # r /\ r2 = r 
                THEN Append(network[r1][r2], [ 
                    type |-> "NewView",
                    view |-> view[r],
                    log |-> log'[r]])
                ELSE network[r1][r2]]]
    \* replica becomes a primary
    /\ primary' = [primary EXCEPT ![r] = TRUE]
    \* primary updates its commit indexes
    \* Crash commit index may be decreased if there's been an byz attack
    /\ crashCommitIndex' = [crashCommitIndex EXCEPT 
        ![r] = Max2(Min2(@, Len(log'[r])), HighestCrashQC(log'[r]))]
    /\ UNCHANGED <<view, byzActions, byzCommitIndex, viewStable>>

\* Replicas will discard messages from previous views or extra view changes messages
\* Note that replicas must always discard messages as the pairwise channels are ordered so a replica may need to discard an out-of-date message to process a more recent one
DiscardMessage(r, s) ==
    /\ network[r][s] # <<>>
    /\ \/ Head(network[r][s]).view < view[r]
       \/ Head(network[r][s]).type = "ViewChange" /\ primary[r]
    /\ network' = [network EXCEPT ![r][s] = Tail(@)]
    /\ UNCHANGED <<view, log, primary, prepareQC, crashCommitIndex, byzCommitIndex, byzActions, viewStable>>

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
    \* we remove the AppendEntries message and reply with a Vote message.
    /\ network' = [network EXCEPT 
        ![r][p] = Tail(@),
        ![p][r] = Append(@,[
            type |-> "Vote",
            view |-> view[r],
            log |-> Head(network[r][p]).log
            ])
        ]
    /\ UNCHANGED <<primary, view, prepareQC, crashCommitIndex, byzCommitIndex, log, viewStable>>

\* Given an append entries message, returns the same message with the txn changed to 1
ModifyAppendEntries(m) == [
    type |-> "AppendEntries",
    view |-> m.view,
    log |-> SubSeq(m.log,1,Len(m.log)-1) \o 
        <<[Last(m.log) EXCEPT !.tx = <<1>>]>>
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
    /\ UNCHANGED <<view, log, primary, prepareQC, crashCommitIndex, byzCommitIndex, viewStable>>

\* Next state relation
\* Note that the byzantine actions are included here but can be disabled by setting MaxByzActions to 0 or BR to {}.
Next == 
    \/ \E r \in BR:
        \/ ByzPrimaryEquivocate(r)
        \/ \E s \in R: \* TODO CR because we don't need byz replicas to receive messages from other byz replicas?!
            ByzOmitEntries(r,s)
    \/ \E r \in R: 
        \/ SendEntries(r)
        \/ Timeout(r)
        \/ BecomePrimary(r)
        \/ \E s \in R: 
            \/ ReceiveEntries(r,s)
            \/ ReceiveVote(r,s)
            \/ ReceiveNewView(r,s)
            \/ DiscardMessage(r,s)

Fairness ==
    \* Only Timeout if there is no primary.
    /\ \A r \in HR: WF_vars(TRUE \notin Range(primary) /\ Timeout(r))
    /\ \A r \in HR: WF_vars(BecomePrimary(r))
    /\ \A r,s \in HR: WF_vars(DiscardMessage(r,s))
    /\ \A r \in HR: WF_vars(SendEntries(r))
    /\ \A r,s \in HR: WF_vars(ReceiveEntries(r,s))
    /\ \A r,s \in HR: WF_vars(ReceiveVote(r,s))
    /\ \A r,s \in HR: WF_vars(ReceiveNewView(r,s))
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
    SubSeq(log[r], 1, crashCommitIndex[r])

\* The view of a log entry is always greater than or equal to the view of the previous entry, i.e.,
\* the view of log entries is (non-strictly) monotonically increasing.
ViewMonotonicInv ==
    \A r \in R :
        \A i \in 2..Len(log[r]) :
            log[r][i].view >= log[r][i-1].view

\* Every view starts with a view stabilization log entry. Moreover, view 0 is always stable.
\* Therefore, view 0 has no view stabilization log entry.
ViewStabilizationInv ==
    \A r \in R :
        /\ \A i \in 1..Len(log[r]) :
            /\ log[r][i].tx = <<>> => log[r][i].view # 0
            /\ i > 1 /\ log[r][i].view > log[r][i-1].view => log[r][i].tx = <<>>

\* Ignoring view stabilization log entries (modeled as empty txs), true iff the log p is a prefix of log l.
IsPrefixWithoutEmpty(p, l) ==
    \* p can be longer than l. Suppose l matches p as a prefix up to index i, but the suffix of p starting
    \* at i+1 contains only view stabilization log entries. By adding the condition Len(p) <= Len(l), we
    \* ensure that such cases are not considered as p being a prefix of l. Instead, we require that l is at
    \* least as long as p, ensuring that l has a suffix distinct from p.
    \* Independently, this condition prevents out-of-bounds access when p is longer than l. For example, if
    \* l = <<>> (an empty sequence), attempting to access l[k] in the disjunct p[k] = l[k] would lead to an
    \* out-of-bounds access.
    /\ Len(p) <= Len(l)
    /\ \A k \in 1..Len(p):
          \/ p[k] = l[k]
          \/ p[k].tx = <<>>

\* If no byzantine actions have been taken, then the committed logs of all replicas must be prefixes of each other
\* This, together with CommittedLogAppendOnlyProp, is the classic CFT safety property
\* Note that if any nodes have been byzantine, then this property is not guaranteed to hold on any node
\* LogInv implies that the byzantine committed logs of replicas are prefixes too, as IndexBoundsInv ensures that the byzCommitIndex is always less than or equal to the crashCommitIndex.
LogInv ==
    byzActions = 0 =>
        \A i, j \in R :
            \/ IsPrefixWithoutEmpty(Committed(i),Committed(j)) 
            \/ IsPrefixWithoutEmpty(Committed(j),Committed(i))

ByzCommitted(r) ==
    SubSeq(log[r], 1, byzCommitIndex[r])

\* Variant of LogInv for the byzantine commit index and correct replicas only
\* We make no assertions about the state of byzantine replicas
ByzLogInv ==
    \A i, j \in CR :
        \/ IsPrefix(ByzCommitted(i),ByzCommitted(j)) 
        \/ IsPrefix(ByzCommitted(j),ByzCommitted(i))

\* If no byzantine actions have been taken, then each replica only appends to its committed log
\* Note that this invariant allows empty blocks (sent at the start of a view) to be rolled back
CommittedLogAppendOnlyProp ==
    [][byzActions = 0 => 
        \A i \in R :
        IsPrefixWithoutEmpty(Committed(i), Committed(i)')]_vars

\* Each correct replica only appends to its byzantine committed log
ByzCommittedLogAppendOnlyProp ==
    [][\A i \in CR :
        IsPrefix(ByzCommitted(i), ByzCommitted(i)')]_vars

\* At most one correct replica is primary in a view
OneLeaderPerTermInv ==
    \A v \in 0..Max(Range(view)), r \in CR :
        view[r] = v /\ primary[r] 
        => \A s \in R \ {r} : view[s] = v => ~primary[s]

IndexBoundsInv ==
    \A r \in CR :
        /\ crashCommitIndex[r] <= Len(log[r])
        /\ byzCommitIndex[r] <= crashCommitIndex[r]

WellFormedLogInv ==
    \A r \in CR : WellFormedLog(log[r])

====