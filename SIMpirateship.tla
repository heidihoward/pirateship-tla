----- MODULE SIMpirateship -----
EXTENDS TLCpirateship, TLC

PS == INSTANCE pirateship

SIMTimeout(r) ==
    \* TODO: revise this
    \* /\ \/ 1 = RandomElement(1..10)
    \*    \/ TRUE \notin Range(primary)
    /\ PS!Timeout(r)

====