----- MODULE SIMpirateship -----
EXTENDS TLCpirateship, TLC, IOUtils

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

====