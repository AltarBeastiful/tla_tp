------------------------------ MODULE euclide ------------------------------

EXTENDS Naturals, TLC
CONSTANT K
Divides(i,j) == \E k \in 0..j: j = i * k
IsGCD(i,j,k) == 
  Divides(i,j)
/\ Divides(i,k)
/\ \A r \in 0..j \cup 0..k :
    (Divides(r,j ) /\ Divides(r,k)) => Divides(r,i)
(* --algorithm EuclidSedgewick
{
    variables m \in 1..K, n \in 1..K, u = m, v = n;
    {
        L1: while (u # 0) {
            if (u < v) { u := v || v := u };
            L2: u := u - v
        };
    assert IsGCD(v, m, n)
    }
}
*)
\* BEGIN TRANSLATION
VARIABLES m, n, u, v, pc

vars == << m, n, u, v, pc >>

Init == (* Global variables *)
        /\ m \in 1..K
        /\ n \in 1..K
        /\ u = m
        /\ v = n
        /\ pc = "L1"

L1 == /\ pc = "L1"
      /\ IF u # 0
            THEN /\ IF u < v
                       THEN /\ /\ u' = v
                               /\ v' = u
                       ELSE /\ TRUE
                            /\ UNCHANGED << u, v >>
                 /\ pc' = "L2"
            ELSE /\ Assert(IsGCD(v, m, n), 
                           "Failure of assertion at line 19, column 5.")
                 /\ pc' = "Done"
                 /\ UNCHANGED << u, v >>
      /\ UNCHANGED << m, n >>

L2 == /\ pc = "L2"
      /\ u' = u - v
      /\ pc' = "L1"
      /\ UNCHANGED << m, n, v >>

Next == L1 \/ L2
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION


=============================================================================
\* Modification History
\* Last modified Fri Nov 21 08:59:10 CET 2014 by legaliz_me
\* Created Fri Nov 21 08:45:37 CET 2014 by legaliz_me
