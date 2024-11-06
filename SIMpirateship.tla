----- MODULE SIMpirateship -----
EXTENDS pirateship, TLC

PS == INSTANCE pirateship

SIMTimeout(r) ==
    /\ 1 = RandomElement(1..10)
    /\ PS!Timeout(r)

====