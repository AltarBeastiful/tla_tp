------------------------------- MODULE crible -------------------------------

EXTENDS Naturals, TLC
CONSTANT K

Divides(i,j) == \E k \in 0..j: j = i * k

IsGCD(i,j,k) == 
  Divides(i,j)
/\ Divides(i,k)
/\ \A r \in 0..j \cup 0..k :
    (Divides(r,j ) /\ Divides(r,k)) => Divides(r,i)

(* --algorithm crible
{
    variable buffer = [i \in 1..K |-> 0], x=3, primes = [i \in 1..K |-> 0], iPrime = 1;
    process (G = 0)
    {   l1: buffer[2] := 2;
        l2: while(x <= K) {
          await(buffer[2] = 0);
          buffer[2] := x;
          x := x + 1;
        }           
    }
    
    process(F \in 2..K)
    variable current = 0, next=0;
    {   
        l3:while(TRUE){
        
            await(buffer[self] # 0);

            l4:if(current = 0) {
                primes[iPrime] := self;
                iPrime := iPrime + 1;
            };

            l5:current := buffer[self];
            buffer[self] := 0;
                       
            l6:if(current % self # 0) {
                if(next = 0) {
                    next := current;
                };
                await(buffer[next] = 0);
                l7:buffer[next] := current;  
            };
        }
    }
    
    
    
    
}
*)
\* BEGIN TRANSLATION
VARIABLES buffer, x, primes, iPrime, pc, current, next

vars == << buffer, x, primes, iPrime, pc, current, next >>

ProcSet == {0} \cup (2..K)

Init == (* Global variables *)
        /\ buffer = [i \in 1..K |-> 0]
        /\ x = 3
        /\ primes = [i \in 1..K |-> 0]
        /\ iPrime = 1
        (* Process F *)
        /\ current = [self \in 2..K |-> 0]
        /\ next = [self \in 2..K |-> 0]
        /\ pc = [self \in ProcSet |-> CASE self = 0 -> "l1"
                                        [] self \in 2..K -> "l3"]

l1 == /\ pc[0] = "l1"
      /\ buffer' = [buffer EXCEPT ![2] = 2]
      /\ pc' = [pc EXCEPT ![0] = "l2"]
      /\ UNCHANGED << x, primes, iPrime, current, next >>

l2 == /\ pc[0] = "l2"
      /\ IF x <= K
            THEN /\ (buffer[2] = 0)
                 /\ buffer' = [buffer EXCEPT ![2] = x]
                 /\ x' = x + 1
                 /\ pc' = [pc EXCEPT ![0] = "l2"]
            ELSE /\ pc' = [pc EXCEPT ![0] = "Done"]
                 /\ UNCHANGED << buffer, x >>
      /\ UNCHANGED << primes, iPrime, current, next >>

G == l1 \/ l2

l3(self) == /\ pc[self] = "l3"
            /\ (buffer[self] # 0)
            /\ pc' = [pc EXCEPT ![self] = "l4"]
            /\ UNCHANGED << buffer, x, primes, iPrime, current, next >>

l4(self) == /\ pc[self] = "l4"
            /\ IF current[self] = 0
                  THEN /\ primes' = [primes EXCEPT ![iPrime] = self]
                       /\ iPrime' = iPrime + 1
                  ELSE /\ TRUE
                       /\ UNCHANGED << primes, iPrime >>
            /\ pc' = [pc EXCEPT ![self] = "l5"]
            /\ UNCHANGED << buffer, x, current, next >>

l5(self) == /\ pc[self] = "l5"
            /\ current' = [current EXCEPT ![self] = buffer[self]]
            /\ buffer' = [buffer EXCEPT ![self] = 0]
            /\ pc' = [pc EXCEPT ![self] = "l6"]
            /\ UNCHANGED << x, primes, iPrime, next >>

l6(self) == /\ pc[self] = "l6"
            /\ IF current[self] % self # 0
                  THEN /\ IF next[self] = 0
                             THEN /\ next' = [next EXCEPT ![self] = current[self]]
                             ELSE /\ TRUE
                                  /\ next' = next
                       /\ (buffer[next'[self]] = 0)
                       /\ pc' = [pc EXCEPT ![self] = "l7"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "l3"]
                       /\ next' = next
            /\ UNCHANGED << buffer, x, primes, iPrime, current >>

l7(self) == /\ pc[self] = "l7"
            /\ buffer' = [buffer EXCEPT ![next[self]] = current[self]]
            /\ pc' = [pc EXCEPT ![self] = "l3"]
            /\ UNCHANGED << x, primes, iPrime, current, next >>

F(self) == l3(self) \/ l4(self) \/ l5(self) \/ l6(self) \/ l7(self)

Next == G
           \/ (\E self \in 2..K: F(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Thu Dec 18 11:03:26 CET 2014 by legaliz_me
\* Created Fri Nov 21 09:10:02 CET 2014 by legaliz_me
