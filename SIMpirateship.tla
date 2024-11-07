----- MODULE SIMpirateship -----
EXTENDS pirateship, TLC

PS == INSTANCE pirateship

SIMTimeout(r) ==
    /\ \/ 1 = RandomElement(1..10)
       \/ TRUE \notin Range(primary)
    /\ PS!Timeout(r)

====