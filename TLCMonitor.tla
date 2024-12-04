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
    (* Count, under the specified name, the number of occurrences where the given expression is true. *)
    TLCModify(TLCMonitorMagicNumber, LAMBDA old, b: 
        IF b
        THEN
            IF name \in DOMAIN old
            THEN [old EXCEPT ![name] = @ + 1]
            ELSE old @@ (name :> 1)
        ELSE old @@ (name :> 0), expr, <<>>)

TLCMonitorMin(expr, name, val) ==
    (* Store the running minimum value under the specified name, the given expression is true, *)
    (* but only update it if the current value is smaller than the previously stored value.    *)
    TLCModify(TLCMonitorMagicNumber, LAMBDA old, b: 
        IF b
        THEN
            IF name \in DOMAIN old
            THEN [old EXCEPT ![name] = IF @ < val THEN @ ELSE val]
            ELSE old @@ (name :> val)
        ELSE old @@ (name :> 2147483647), expr, <<>>) \* 2^31 - 1 is TLC's max value.

TLCMonitors ==
    \* Merge values of *all* workers.
    FoldSeq(LAMBDA f, g : [ k \in DOMAIN f |-> IF f[k] = 2147483647 THEN 0 ELSE f[k] + IF k \in DOMAIN g THEN g[k] ELSE 0 ], 
                <<>>, TLCGet("all")[TLCMonitorMagicNumber])

TLCCheckMonitors ==
    (\E name \in DOMAIN TLCMonitors: TLCMonitors[name] = 0) => Print(TLCMonitors, FALSE)

TLCPrintMonitors ==
    PrintT(TLCMonitors)

================================