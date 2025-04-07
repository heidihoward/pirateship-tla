----- MODULE TLCpirateship -----
EXTENDS pirateship, TLC

PS == INSTANCE pirateship

TLCInit ==
    \/ PS!Init
    \* Cluster is in a steady state.
    \/ /\ view = [r \in R |-> 0]
       /\ byzActions = 0
       /\ network = [r \in R |-> [s \in R |-> <<>>]]
       /\ byzCommitIndex = [r \in R |-> 2]
       /\ \E p \in R:
             /\ primary = [ r \in R |-> r = p ]
             /\ viewStable = primary \* Identical to primary at startup.
             /\ log = [r \in R |-> 
                    <<[view |-> 0, tx |-> <<1>>, byzQC |-> {},  byzQCVotes |-> {},  crashQC |-> {}],
                      [view |-> 0, tx |-> <<1>>, byzQC |-> {},  byzQCVotes |-> {},  crashQC |-> {}],
                      [view |-> 0, tx |-> <<1>>, byzQC |-> {1}, byzQCVotes |-> R,  crashQC |-> {1}],
                      [view |-> 0, tx |-> <<1>>, byzQC |-> {2}, byzQCVotes |-> R,  crashQC |-> {2}]>>]
             /\ prepareQC = [r \in R |-> [s \in R |-> IF r = p THEN Len(log[r]) ELSE 0]]
             /\ commitIndex = [r \in R |-> Len(log[r])]

-----

\* Add a few monitors/canaries to check if interesting states are reachable.

Monitors == INSTANCE TLCMonitor WITH TLCMonitorMagicNumber <- 0

CrashCommitIndexAt1 ==
   Monitors!TLCMonitor(\A r \in HR: commitIndex[r] = 1, "CrashCommitIndex@1")

CrashCommitIndexAt2 ==
   Monitors!TLCMonitor(\A r \in HR: commitIndex[r] = 2, "CrashCommitIndex@2")

CrashCommitIndex1AtLevel ==
    Monitors!TLCMonitorMin(\A r \in HR: commitIndex[r] = 1, "CrashCommitIndex1AtLevel", TLCGet("level"))

CrashCommitIndex2AtLevel ==
    Monitors!TLCMonitorMin(\A r \in HR: commitIndex[r] = 2, "CrashCommitIndex2AtLevel", TLCGet("level"))

ByzCommitIndexAt1 ==
   Monitors!TLCMonitor(\A r \in HR: byzCommitIndex[r] = 1, "ByzCommitIndex@1")

ByzCommitIndexAt2 ==
   Monitors!TLCMonitor(\A r \in HR: byzCommitIndex[r] = 2, "ByzCommitIndex@2")

ByzCommitIndex1AtLevel ==
    Monitors!TLCMonitorMin(\A r \in HR: byzCommitIndex[r] = 1, "ByzCommitIndex1AtLevel", TLCGet("level"))

ByzCommitIndex2AtLevel ==
    Monitors!TLCMonitorMin(\A r \in HR: byzCommitIndex[r] = 2, "ByzCommitIndex2AtLevel", TLCGet("level"))

MonitorPostcondition ==
    Monitors!TLCCheckMonitors

PrintMonitors ==
    Monitors!TLCPrintMonitors

-----

DebugCrashCommitIndex ==
    \* For all replicas, commitIndex is always less than two.
    \E i \in Range(commitIndex): i < 2

DebugByzCommitIndex ==
    \* For all replicas, byzCommitIndex is always less than two.
    \E i \in Range(byzCommitIndex): i < 2

=====