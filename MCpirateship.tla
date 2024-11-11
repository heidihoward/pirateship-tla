---- MODULE MCpirateship ----
EXTENDS TLCpirateship

CONSTANT MCViews

PS == INSTANCE pirateship

MCTimeout(r) ==
    \* artifact of the spec, check that the view limit is not exceeded
    /\ view[r] + 1 \in MCViews
    /\ PS!Timeout(r)

=====