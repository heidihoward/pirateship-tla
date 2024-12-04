----- MODULE SIMpirateship -----
EXTENDS TLCpirateship, TLC

SIMTimeout(r) ==
    /\ \/ 1 = RandomElement(1..10)
       \* There is no primary in the highest view.
       \/ LET S == { s \in R : view[s] = Max(Range(view))} 
          IN TRUE \notin Range([ s \in S |-> primary[s] ])
    /\ PS!Timeout(r)

====