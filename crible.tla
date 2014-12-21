------------------------------- MODULE crible -------------------------------

EXTENDS Naturals, TLC
CONSTANT K

Divides(i,j) == \E k \in 0..j: j = i * k

IsGCD(i,j,k) == 
  Divides(i,j)
/\ Divides(i,k)
/\ \A r \in 0..j \cup 0..k :
    (Divides(r,j ) /\ Divides(r,k)) => Divides(r,i)
    
IsPrime (x) ==
\A i \in 1..x :
    Divides(x,i) => i = 1 \/ i = x
   

(* --algorithm crible
{
    variable buffer = [i \in 1..K+1 |-> 0], x=3, primes = [i \in 1..K |-> 0], iPrime = 1;
    process (G = 0)
    {   
        l1: buffer[2] := 2;
        l2: while(x <= K) {
          await(buffer[2] = 0);
          buffer[2] := x;
          x := x + 1;
        };
        
        await(buffer[2] = 0);
        buffer[2] := 1;
        
        \*assert FALSE;         
    }  
    
    process(F \in 2..K)
    variable current = 0, next=0, firstValue = 1, continue = 1;
    {   
         
        l3:while(continue = 1){
        
            l11: receive(self, current);
            
            
            checkdone:if(buffer[self] = 1) {
                continue := 0;
                buffer[self] := 0;
                check:await(buffer[self + 1] = 0);
                buffer[self + 1] := 1;
            } else {

                l4:if(firstValue = 1) {
                    
                    print self;
                    firstValue := 0;
                    primes[self] := self;
                    
                    assert IsPrime(self);
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
            };
        };
    }  
    
      
}

macro receive(i, value) {
    await(buffer[i] # 0);
    value := buffer[i];
    buffer[i] := 0;
};  

   macro Send(m, chan) { chan := Append(chan,m) }

 

*)
\* BEGIN TRANSLATION
VARIABLES buffer, x, primes, iPrime, pc, current, next, firstValue, continue

vars == << buffer, x, primes, iPrime, pc, current, next, firstValue, continue
        >>

ProcSet == {0} \cup (2..K)

Init == (* Global variables *)
        /\ buffer = [i \in 1..K+1 |-> 0]
        /\ x = 3
        /\ primes = [i \in 1..K |-> 0]
        /\ iPrime = 1
        (* Process F *)
        /\ current = [self \in 2..K |-> 0]
        /\ next = [self \in 2..K |-> 0]
        /\ firstValue = [self \in 2..K |-> 1]
        /\ continue = [self \in 2..K |-> 1]
        /\ pc = [self \in ProcSet |-> CASE self = 0 -> "l1"
                                        [] self \in 2..K -> "l3"]

l1 == /\ pc[0] = "l1"
      /\ buffer' = [buffer EXCEPT ![2] = 2]
      /\ pc' = [pc EXCEPT ![0] = "l2"]
      /\ UNCHANGED << x, primes, iPrime, current, next, firstValue, continue >>

l2 == /\ pc[0] = "l2"
      /\ IF x <= K
            THEN /\ (buffer[2] = 0)
                 /\ buffer' = [buffer EXCEPT ![2] = x]
                 /\ x' = x + 1
                 /\ pc' = [pc EXCEPT ![0] = "l2"]
            ELSE /\ (buffer[2] = 0)
                 /\ buffer' = [buffer EXCEPT ![2] = 1]
                 /\ pc' = [pc EXCEPT ![0] = "Done"]
                 /\ x' = x
      /\ UNCHANGED << primes, iPrime, current, next, firstValue, continue >>

G == l1 \/ l2

l3(self) == /\ pc[self] = "l3"
            /\ IF continue[self] = 1
                  THEN /\ pc' = [pc EXCEPT ![self] = "l11"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << buffer, x, primes, iPrime, current, next, 
                            firstValue, continue >>

l11(self) == /\ pc[self] = "l11"
             /\ (buffer[self] # 0)
             /\ pc' = [pc EXCEPT ![self] = "checkdone"]
             /\ UNCHANGED << buffer, x, primes, iPrime, current, next, 
                             firstValue, continue >>

checkdone(self) == /\ pc[self] = "checkdone"
                   /\ IF buffer[self] = 1
                         THEN /\ continue' = [continue EXCEPT ![self] = 0]
                              /\ buffer' = [buffer EXCEPT ![self] = 0]
                              /\ pc' = [pc EXCEPT ![self] = "check"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "l4"]
                              /\ UNCHANGED << buffer, continue >>
                   /\ UNCHANGED << x, primes, iPrime, current, next, 
                                   firstValue >>

check(self) == /\ pc[self] = "check"
               /\ (buffer[self + 1] = 0)
               /\ buffer' = [buffer EXCEPT ![self + 1] = 1]
               /\ pc' = [pc EXCEPT ![self] = "l3"]
               /\ UNCHANGED << x, primes, iPrime, current, next, firstValue, 
                               continue >>

l4(self) == /\ pc[self] = "l4"
            /\ IF firstValue[self] = 1
                  THEN /\ PrintT(self)
                       /\ firstValue' = [firstValue EXCEPT ![self] = 0]
                       /\ primes' = [primes EXCEPT ![self] = self]
                       /\ Assert(IsPrime(self), 
                                 "Failure of assertion at line 58, column 21.")
                  ELSE /\ TRUE
                       /\ UNCHANGED << primes, firstValue >>
            /\ pc' = [pc EXCEPT ![self] = "l5"]
            /\ UNCHANGED << buffer, x, iPrime, current, next, continue >>

l5(self) == /\ pc[self] = "l5"
            /\ current' = [current EXCEPT ![self] = buffer[self]]
            /\ buffer' = [buffer EXCEPT ![self] = 0]
            /\ pc' = [pc EXCEPT ![self] = "l6"]
            /\ UNCHANGED << x, primes, iPrime, next, firstValue, continue >>

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
            /\ UNCHANGED << buffer, x, primes, iPrime, current, firstValue, 
                            continue >>

l7(self) == /\ pc[self] = "l7"
            /\ buffer' = [buffer EXCEPT ![next[self]] = current[self]]
            /\ pc' = [pc EXCEPT ![self] = "l3"]
            /\ UNCHANGED << x, primes, iPrime, current, next, firstValue, 
                            continue >>

F(self) == l3(self) \/ l11(self) \/ checkdone(self) \/ check(self)
              \/ l4(self) \/ l5(self) \/ l6(self) \/ l7(self)

Next == G
           \/ (\E self \in 2..K: F(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Sun Dec 21 11:29:26 CET 2014 by legaliz_me
\* Created Fri Nov 21 09:10:02 CET 2014 by legaliz_me
