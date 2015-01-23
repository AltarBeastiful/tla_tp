------------------------------- MODULE arbre -------------------------------
EXTENDS Naturals, TLC, Sequences, FiniteSets

CONSTANTS
    NODES, \* 5
    NEIGHBORGS \* << <<3>>, <<1,4>>, <<2,4,5>>, <<5>>, <<>> >>
    
\*estArbre(a) == ?, il a une et une seule racine, tous les noeuds sont atteignables de la racine,   
\*estArbreSolution(a) == ? si contient tous les noeuds

Parent(n,a) ==
    CHOOSE y \in 1..NODES : a[n] = y

EstRacine(n,a) ==
      a[n] = 0
    
RECURSIVE Atteignable(_,_)  
Atteignable(n,a) == 
 \/ EstRacine(n,a)
 \/ Atteignable(Parent(n,a),a)

EstArbre(a) == \A i \in 1..NODES : Atteignable(i,a)
/\ \E j \in 1..NODES : \A k \in 1..NODES : /\ EstRacine(j,a) 
                                           /\ EstRacine(k,a) => k = j

\* \E i \in 1..NODES : arbre[i] = 0 /\ arbre[n] = i
\* \/ Atteignable(arbre[n], arbre)

(* --algorithm arbre
{
    variable chans = [i \in 1..NODES |-> <<>>],parents = [j \in 1..NODES |-> 0],  start = 0;
    
    macro Send(m, chan) { chan := Append(chan,m) }

    macro Rcv(v, chan) 
    {
        await chan # <<>>;
        v := Head(chan);
        chan := Tail (chan)
    }
    
    process(I = 0)
    variable l = 2;
    {
        l1:Send(0, chans[1]);
        
        wait:while(l <= NODES) {
            await(parents[l] # 0);
            l := l + 1;
        };
                
        check:assert EstArbre(parents);
    }
    
    process(Node \in 1..NODES)
    variable k = 0, childs = <<>>;
    {
        init: Rcv(parents[self], chans[self]);
        
        l2:childs := NEIGHBORGS[self];
        l3:while(Len(childs) > 0) {
            sendToNeigh:Send(self+1, chans[Head(childs)]);
            childs := Tail(childs);
            k := k + 1;
        };
    }
}

*)
\* BEGIN TRANSLATION
VARIABLES chans, parents, start, pc, l, k, childs

vars == << chans, parents, start, pc, l, k, childs >>

ProcSet == {0} \cup (1..NODES)

Init == (* Global variables *)
        /\ chans = [i \in 1..NODES |-> <<>>]
        /\ parents = [j \in 1..NODES |-> 0]
        /\ start = 0
        (* Process I *)
        /\ l = 2
        (* Process Node *)
        /\ k = [self \in 1..NODES |-> 0]
        /\ childs = [self \in 1..NODES |-> <<>>]
        /\ pc = [self \in ProcSet |-> CASE self = 0 -> "l1"
                                        [] self \in 1..NODES -> "init"]

l1 == /\ pc[0] = "l1"
      /\ chans' = [chans EXCEPT ![1] = Append((chans[1]),0)]
      /\ pc' = [pc EXCEPT ![0] = "wait"]
      /\ UNCHANGED << parents, start, l, k, childs >>

wait == /\ pc[0] = "wait"
        /\ IF l <= NODES
              THEN /\ (parents[l] # 0)
                   /\ l' = l + 1
                   /\ pc' = [pc EXCEPT ![0] = "wait"]
              ELSE /\ pc' = [pc EXCEPT ![0] = "check"]
                   /\ l' = l
        /\ UNCHANGED << chans, parents, start, k, childs >>

check == /\ pc[0] = "check"
         /\ Assert(EstArbre(parents), 
                   "Failure of assertion at line 52, column 15.")
         /\ pc' = [pc EXCEPT ![0] = "Done"]
         /\ UNCHANGED << chans, parents, start, l, k, childs >>

I == l1 \/ wait \/ check

init(self) == /\ pc[self] = "init"
              /\ (chans[self]) # <<>>
              /\ parents' = [parents EXCEPT ![self] = Head((chans[self]))]
              /\ chans' = [chans EXCEPT ![self] = Tail ((chans[self]))]
              /\ pc' = [pc EXCEPT ![self] = "l2"]
              /\ UNCHANGED << start, l, k, childs >>

l2(self) == /\ pc[self] = "l2"
            /\ childs' = [childs EXCEPT ![self] = NEIGHBORGS[self]]
            /\ pc' = [pc EXCEPT ![self] = "l3"]
            /\ UNCHANGED << chans, parents, start, l, k >>

l3(self) == /\ pc[self] = "l3"
            /\ IF Len(childs[self]) > 0
                  THEN /\ pc' = [pc EXCEPT ![self] = "sendToNeigh"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << chans, parents, start, l, k, childs >>

sendToNeigh(self) == /\ pc[self] = "sendToNeigh"
                     /\ chans' = [chans EXCEPT ![Head(childs[self])] = Append((chans[Head(childs[self])]),(self+1))]
                     /\ childs' = [childs EXCEPT ![self] = Tail(childs[self])]
                     /\ k' = [k EXCEPT ![self] = k[self] + 1]
                     /\ pc' = [pc EXCEPT ![self] = "l3"]
                     /\ UNCHANGED << parents, start, l >>

Node(self) == init(self) \/ l2(self) \/ l3(self) \/ sendToNeigh(self)

Next == I
           \/ (\E self \in 1..NODES: Node(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Fri Jan 23 14:12:22 CET 2015 by remi
\* Created Fri Jan 09 09:00:07 CET 2015 by remi
