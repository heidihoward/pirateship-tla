---- MODULE ActionConstraint ----
EXTENDS pirateship, TLC

CONSTANT a,b,c,Z

_actionConstraint ==
LET _idx == TLCGet("level") IN
\/ 1 = _idx /\ SendEntries(a)
\/ 2 = _idx /\ ReceiveEntries(Z, a)
\/ 3 = _idx /\ ReceiveEntries(b, a)
\/ 4 = _idx /\ ReceiveVote(a, Z)
\/ 5 = _idx /\ Timeout(b)
\/ 6 = _idx /\ ReceiveVote(a, b)
\/ 7 = _idx /\ SendEntries(a)
\/ 8 = _idx /\ Timeout(Z)
\/ 9 = _idx /\ Timeout(a)
\/ 10 = _idx /\ Timeout(a)
\/ 11 = _idx /\ ReceiveEntries(c, a)
\/ 12 = _idx /\ Timeout(c)
\/ 13 = _idx /\ BecomePrimary(b)
\/ 14 = _idx /\ DiscardMessage(c, a)
\/ 15 = _idx /\ ReceiveNewView(Z, b)
\/ 16 = _idx /\ SendEntries(b)
\/ 17 = _idx /\ ReceiveNewView(c, b)
\/ 18 = _idx /\ ReceiveEntries(c, b)
\/ 19 = _idx /\ ReceiveVote(b, Z)
\/ 20 = _idx /\ ReceiveVote(b, c)
\/ 21 = _idx /\ ReceiveEntries(Z, b)
\/ 22 = _idx /\ Timeout(Z)
\/ 23 = _idx /\ Timeout(c)
\/ 24 = _idx /\ BecomePrimary(c)
\/ 25 = _idx /\ ReceiveVote(b, Z)
\/ 26 = _idx /\ ReceiveVote(b, c)

====