----- MODULE TLCpirateship -----
EXTENDS pirateship, TLC

\* Add a few monitors/canaries to check if interesting states are reachable.

Monitors == INSTANCE TLCMonitor WITH TLCMonitorMagicNumber <- 0

CrashCommitIndexAt1 ==
   Monitors!TLCMonitor(\A r \in HR: crashCommitIndex[r] = 1, "CrashCommitIndex@1")

CrashCommitIndexAt2 ==
   Monitors!TLCMonitor(\A r \in HR: crashCommitIndex[r] = 2, "CrashCommitIndex@2")

CrashCommitIndex1AtLevel ==
    Monitors!TLCMonitorMin(\A r \in HR: crashCommitIndex[r] = 1, "CrashCommitIndex1AtLevel", TLCGet("level"))

CrashCommitIndex2AtLevel ==
    Monitors!TLCMonitorMin(\A r \in HR: crashCommitIndex[r] = 2, "CrashCommitIndex2AtLevel", TLCGet("level"))

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

=====