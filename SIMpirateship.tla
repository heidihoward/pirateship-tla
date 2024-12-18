----- MODULE SIMpirateship -----
EXTENDS TLCpirateship, TLC, TLCExt, CSV, IOUtils

SIMTimeout(r) ==
    /\ \/ 1 = RandomElement(1..((TLCGet("duration") % 300)+1)) \* Adjust probability of timeouts as a function of the duration of the simulation.
       \* There is no primary in the highest view.
       \/ LET S == { s \in R : view[s] = Max(Range(view))} 
          IN TRUE \notin Range([ s \in S |-> primary[s] ])
    /\ PS!Timeout(r)

-----

SerializeStats ==
    \* Run simulation with -Dtlc2.tool.Simulator.extendedStatistics=true to collect extended statistics.
    Serialize(<<TLCGet("stats")>>, "SIMpirateship.ndjson", [format |-> "NDJSON", charset |-> "UTF-8", openOptions |-> <<"WRITE", "CREATE", "APPEND">>])

SIMPostCondition ==
    /\ SerializeStats
    /\ MonitorPostcondition

SIMPeriodic ==
    /\ SerializeStats
    /\ PrintMonitors

-----

StatsFastPath ==
    1 + (TLCGet("stats").behavior.id % 3) \* +1 to avoid collision with TLCpirateship!TLCMonitorMagicNumber

StatsHighestUnanimity(l, i, r) ==
    LET fastPath == StatsFastPath IN
    \* No fast path
    IF fastPath = 1 THEN {0}
    \* Non-transitive fast path, i.e, one unanimous QC.
    ELSE IF fastPath = 2 THEN LET idx == SelectLastInSeq(l, LAMBDA e: e.byzQCVotes = R) IN IF idx = 0 THEN {0} ELSE l[idx].byzQC
    \* Transitive fast path, i.e., combined votes from all applicable QCs.
    ELSE HighestUnanimity(l, i, r)

StatsConstraint ==
    \* Average the number of uncommitted (byzantine) transactions accross all replicas. 
    LET Sum == FoldFunction(+, 0, [ r \in R |-> Len(log[r]) - byzCommitIndex[r] ])
    \* When done with the current behavior...
    IN (TLCGet("level") = TLCGet("config").depth) => 
            TLCGetAndSet(StatsFastPath, 
                        LAMBDA old, val:
                            \* Update the average (sum/observations) of uncommitted transactions.
                            [ sum |-> old.sum + val, obs |-> old.obs + 1 ], 
                        Sum, [sum |-> 0, obs |-> 0])
                            \in [sum : Nat, obs : Nat] \* Always evaluate/equal to TRUE.

StatsPostcondition ==
    \* Merge the average of each fastPath value accross all TLC workers.
    /\ LET CSVFile == "StatsSIMpirateship.csv"
           v ==[ key \in DOMAIN TLCGet("all") |-> 
            FoldFunction(
                    LAMBDA val, acc: [sum|->acc.sum+val.sum, obs|->acc.obs+val.obs], 
                    [sum |-> 0, obs |-> 0], TLCGet("all")[key]) ] IN
        /\ PrintT([ key \in DOMAIN v |-> <<key, v[key].sum \div v[key].obs>>])
        /\ CSVRecords(CSVFile) = 0 => CSVWrite("fastPath#sum#observations", <<>>, CSVFile)
        /\ \A key \in DOMAIN v:
                CSVWrite("%1$s#%2$s#%3$s", <<key, v[key].sum, v[key].obs>>, CSVFile)

====