---- MODULE MCpirateship ----
EXTENDS pirateship, TLC

CONSTANT MCViews

PS == INSTANCE pirateship

MCTimeout(r) ==
    \* artifact of the spec, check that the view limit is not exceeded
    /\ view[r] + 1 \in MCViews
    /\ PS!Timeout(r)    

\* https://github.com/heidihoward/pirateship-tla/issues/7
ASSUME Cardinality(MCViews) = 5
CONSTANT a, b, c, Z
ActionConstraintGH07 ==
    LET t ==
        <<  SendEntries(a)
            ,ReceiveEntries(b,a)
            ,ReceiveEntries(c,a)
            
            ,Timeout(a)
            ,Timeout(a)
            ,Timeout(a)
            ,Timeout(a)
            ,Timeout(b)
            ,Timeout(b)
            ,Timeout(b)
            ,Timeout(b)
            ,Timeout(Z)
            ,Timeout(Z)
            ,Timeout(Z)
            ,Timeout(Z)

            ,DiscardMessage(a,b)
            ,DiscardMessage(b,a)

            ,BecomePrimary(a)
            ,ReceiveNewLeader(b,a)

            ,SendEntries(a)
            ,ReceiveEntries(b,a)

            ,ReceiveVote(a,c)
            ,ReceiveVote(a,b)
            ,ReceiveVote(a,b)

            ,SendEntries(a)
        >> 
    IN TLCGet("level") <= Len(t) => t[TLCGet("level")]

Alias ==
    [
        network |-> network
        ,primary |-> primary
        ,view |-> view
        ,log |-> log
        ,matchIndex |-> matchIndex
        ,crashCommitIndex |-> crashCommitIndex
        \* Remain unchanged:
        \* ,byzCommitIndex |-> byzCommitIndex
        \* ,byzActions |-> byzActions
    ]
=====