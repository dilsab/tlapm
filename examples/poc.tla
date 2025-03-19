---- MODULE poc ----
EXTENDS FiniteSetTheorems

THEOREM TRUE
    <1>1. TRUE OBVIOUS 
    <1>2. TRUE OBVIOUS 
    <1>q. QED BY <1>1, <1>2

THEOREM TRUE
    <1>q. QED BY TRUE


THEOREM ProveImplicationDirect ==
    ASSUME NEW A, NEW B PROVE A => B
    PROOF
    <1>1. ASSUME A PROVE B PROOF OMITTED
    <1>q. QED BY <1>1


=======================================================
