------------------------------- MODULE hello -------------------------------

EXTENDS TLC
(* --algorithm HelloWorld
    {
        {   print "Hello, world.";
            assert FALSE
        }
    }
*)
\* BEGIN TRANSLATION
VARIABLE pc

vars == << pc >>

Init == /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ PrintT("Hello, world.")
         /\ Assert(FALSE, "Failure of assertion at line 7, column 13.")
         /\ pc' = "Done"

Next == Lbl_1
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Fri Nov 21 08:49:49 CET 2014 by legaliz_me
\* Created Fri Nov 21 08:36:19 CET 2014 by legaliz_me
