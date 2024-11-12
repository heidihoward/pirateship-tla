---------- MODULE APApirateship ----------

R ==
    {"0_OF_REPLICA", "1_OF_REPLICA", "2_OF_REPLICA"}

BR ==
    {}

Txs ==
    {0,1}

MaxByzActions ==
    0

Primary(v) ==
    "0_OF_REPLICA" \*TODO

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