----- MODULE SIMpirateship -----
EXTENDS TLCpirateship, TLC

SIMTimeout(r) ==
    /\ \/ 1 = RandomElement(1..((TLCGet("duration") % 300)+1)) \* Adjust probability of timeouts as a function of the duration of the simulation.
       \* There is no primary in the highest view.
       \/ LET S == { s \in R : view[s] = Max(Range(view))} 
          IN TRUE \notin Range([ s \in S |-> primary[s] ])
    /\ PS!Timeout(r)

====