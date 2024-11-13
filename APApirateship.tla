---------- MODULE APApirateship ----------
EXTENDS Integers

R ==
    {"0_OF_REPLICA", "1_OF_REPLICA", "2_OF_REPLICA"}

BR ==
    {"3_OF_REPLICA"}

Txs ==
    {0,1}

MaxByzActions ==
    1

Primary(v) ==
    IF v % 4 = 0 THEN "0_OF_REPLICA" ELSE
    IF v % 4 = 1 THEN "1_OF_REPLICA" ELSE
    IF v % 4 = 2 THEN "2_OF_REPLICA" ELSE
                      "3_OF_REPLICA"

Quorums ==
    \* {q \in SUBSET R: Cardinality(q) >= 3}
    {
        {"0_OF_REPLICA", "1_OF_REPLICA", "2_OF_REPLICA"}, 
        {"0_OF_REPLICA", "1_OF_REPLICA", "3_OF_REPLICA"},
        {"0_OF_REPLICA", "2_OF_REPLICA", "3_OF_REPLICA"},
        {"1_OF_REPLICA", "2_OF_REPLICA", "3_OF_REPLICA"},
        {"0_OF_REPLICA", "1_OF_REPLICA", "2_OF_REPLICA","3_OF_REPLICA"}
    }

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

INSTANCE pirateship
======