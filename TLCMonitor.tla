See https://github.com/tlaplus/tlaplus/issues/860

-------- MODULE TLCMonitor ---------
LOCAL INSTANCE TLC
LOCAL INSTANCE TLCExt
LOCAL INSTANCE Naturals
LOCAL INSTANCE SequencesExt

CONSTANT TLCMonitorMagicNumber

ASSUME
    \* Try to claim TLC register `TLCMonitorMagicNumber`.
    /\ TLCGetOrDefault(TLCMonitorMagicNumber, "_TLCMonitorMagicNumber") = "_TLCMonitorMagicNumber"
    /\ TLCSet(TLCMonitorMagicNumber, <<>>)

LOCAL TLCModify(key, Op(_,_), val, defaultVal) ==
    TLCSet(key, Op(TLCGetOrDefault(key, defaultVal), val))

TLCMonitor(expr, name) ==
    TLCModify(TLCMonitorMagicNumber, LAMBDA old, b: 
        IF b
        THEN
            IF name \in DOMAIN old
            THEN [old EXCEPT ![name] = @ + 1]
            ELSE old @@ (name :> 1)
        ELSE old @@ (name :> 0), expr, <<>>)

TLCMonitors ==
    \* Merge values of *all* workers.
    FoldSeq(LAMBDA f, g : [ k \in DOMAIN f |-> f[k] + IF k \in DOMAIN g THEN g[k] ELSE 0 ], 
                <<>>, TLCGet("all")[TLCMonitorMagicNumber])

TLCCheckMonitors ==
    (\E name \in DOMAIN TLCMonitors: TLCMonitors[name] = 0) => Print(TLCMonitors, FALSE)

TLCPrintMonitors ==
    PrintT(TLCMonitors)

================================