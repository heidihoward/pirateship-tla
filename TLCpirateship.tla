----- MODULE TLCpirateship -----
EXTENDS pirateship, Functions


ReplicaSeq ==
    CHOOSE s \in [ 1..N -> R ]: Range(s) = R

MCPrimary(v) ==
    ReplicaSeq[(v % N) + 1]

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

=====