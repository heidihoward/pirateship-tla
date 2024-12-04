---- MODULE ActionConstraint ----
EXTENDS pirateship, TLC

CONSTANT a,b,c,Z

_actionConstraint ==
LET _idx == TLCGet("level") IN
\/ 1 = _idx /\ Timeout(b)
\/ 2 = _idx /\ Timeout(c)
\/ 3 = _idx /\ Timeout(a)
\/ 4 = _idx /\ BecomePrimary(b)
\/ 5 = _idx /\ ReceiveNewView(Z, b)
\/ 6 = _idx /\ ReceiveNewView(a, b)
\/ 7 = _idx /\ ReceiveVote(b, a)
\/ 8 = _idx /\ ReceiveNewView(c, b)
\/ 9 = _idx /\ Timeout(c)
\/ 10 = _idx /\ Timeout(a)
\/ 11 = _idx /\ Timeout(Z)
\/ 12 = _idx /\ BecomePrimary(c)
\/ 13 = _idx /\ ReceiveNewView(Z, c)
\/ 14 = _idx /\ ReceiveNewView(a, c)
\/ 15 = _idx /\ ReceiveVote(b, c)
\/ 16 = _idx /\ SendEntries(b)
\/ 17 = _idx /\ Timeout(a)
\/ 18 = _idx /\ Timeout(b)
\/ 19 = _idx /\ Timeout(b)
\/ 20 = _idx /\ ReceiveVote(c, Z)
\/ 21 = _idx /\ Timeout(Z)
\/ 22 = _idx /\ ReceiveVote(c,a)
\/ 23 = _idx /\ DiscardMessage(Z,b)
\/ 24 = _idx /\ BecomePrimary(Z)

====