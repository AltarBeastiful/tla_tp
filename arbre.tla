------------------------------- MODULE arbre -------------------------------
EXTENDS Naturals, TLC, Sequences

CONSTANTS
    NODES,
    NEIGHBOURS \* 
    
\*estArbre(a) == ?
\*estArbreSolution(a) == ? si contient tous les noeuds

(* --algorithm arbre
{
    variable buffer = [i \in 1..NODES |-> <<>>];
    
    process(I = 0)
    {
        l1:assert TRUE;
    }
    
    process(Node \in 1..NODES)
    {
        l2:assert TRUE;
    }

}

*)
\* BEGIN TRANSLATION
VARIABLES buffer, pc

vars == << buffer, pc >>

ProcSet == {0} \cup (1..NODES)

Init == (* Global variables *)
        /\ buffer = [i \in 1..NODES |-> <<>>]
        /\ pc = [self \in ProcSet |-> CASE self = 0 -> "l1"
                                        [] self \in 1..NODES -> "l2"]

l1 == /\ pc[0] = "l1"
      /\ Assert(TRUE, "Failure of assertion at line 17, column 12.")
      /\ pc' = [pc EXCEPT ![0] = "Done"]
      /\ UNCHANGED buffer

I == l1

l2(self) == /\ pc[self] = "l2"
            /\ Assert(TRUE, "Failure of assertion at line 22, column 12.")
            /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED buffer

Node(self) == l2(self)

Next == I
           \/ (\E self \in 1..NODES: Node(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Fri Jan 09 09:23:21 CET 2015 by remi
\* Created Fri Jan 09 09:00:07 CET 2015 by remi
