------------------------------- MODULE arbre -------------------------------
EXTENDS Naturals, TLC, Sequences

CONSTANTS
    NODES, \* 5
    NEIGHBORGS \* << <<3>>, <<1,4>>, <<2,4,5>>, <<5>>, <<>> >>
    
\*estArbre(a) == ?, il a une et une seule racine, tous les noeuds sont atteignables de la racine,   
\*estArbreSolution(a) == ? si contient tous les noeuds

EstArbre(a) ==
   \E i \in 0..NODES-1 : a[i] = 0

    

(* --algorithm arbre
{
    variable chans = [i \in 1..NODES |-> <<>>], parents = [j \in 1..NODES |-> 0], start = 0;
    
    macro Send(m, chan) { chan := Append(chan,m) }

    macro Rcv(v, chan) 
    {
        await chan # <<>>;
        v := Head(chan);
        chan := Tail (chan)
    }
    
    \*with (i \in 1.. Len(chan)) { chan := Remove(i , chan) }
    
\*    macro Remove(i,seq) == [ j \in 1.. (Len(seq) - 1) \mapsto
\*                            IF j < i THEN seq[j ] ELSE seq[j + 1]]   
    
    process(I = 0)
    variable l = 2;
    {
        l1:Send(0, chans[1]);
        
        wait:while(l <= NODES) {
            await(parents[l] # 0);
            l := l + 1;
        };
        
        assert FALSE;
    }
    
    process(Node \in 1..NODES)
    variable parent=0, k = 0, childs = <<>>;
    {
        init: Rcv(parent, chans[self]);
        parents[self] := parent;
        
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
VARIABLES chans, parents, start, pc, l, parent, k, childs

vars == << chans, parents, start, pc, l, parent, k, childs >>

ProcSet == {0} \cup (1..NODES)

Init == (* Global variables *)
        /\ chans = [i \in 1..NODES |-> <<>>]
        /\ parents = [j \in 1..NODES |-> 0]
        /\ start = 0
        (* Process I *)
        /\ l = 1
        (* Process Node *)
        /\ parent = [self \in 1..NODES |-> 0]
        /\ k = [self \in 1..NODES |-> 0]
        /\ childs = [self \in 1..NODES |-> <<>>]
        /\ pc = [self \in ProcSet |-> CASE self = 0 -> "l1"
                                        [] self \in 1..NODES -> "init"]

l1 == /\ pc[0] = "l1"
      /\ chans' = [chans EXCEPT ![1] = Append((chans[1]),0)]
      /\ pc' = [pc EXCEPT ![0] = "wait"]
      /\ UNCHANGED << parents, start, l, parent, k, childs >>

wait == /\ pc[0] = "wait"
        /\ IF l <= NODES
              THEN /\ (parents[l] # 0)
                   /\ l' = l + 1
                   /\ pc' = [pc EXCEPT ![0] = "wait"]
              ELSE /\ Assert(FALSE, 
                             "Failure of assertion at line 44, column 9.")
                   /\ pc' = [pc EXCEPT ![0] = "Done"]
                   /\ l' = l
        /\ UNCHANGED << chans, parents, start, parent, k, childs >>

I == l1 \/ wait

init(self) == /\ pc[self] = "init"
              /\ (chans[self]) # <<>>
              /\ parent' = [parent EXCEPT ![self] = Head((chans[self]))]
              /\ chans' = [chans EXCEPT ![self] = Tail ((chans[self]))]
              /\ parents' = [parents EXCEPT ![self] = parent'[self]]
              /\ pc' = [pc EXCEPT ![self] = "l2"]
              /\ UNCHANGED << start, l, k, childs >>

l2(self) == /\ pc[self] = "l2"
            /\ childs' = [childs EXCEPT ![self] = NEIGHBORGS[self]]
            /\ pc' = [pc EXCEPT ![self] = "l3"]
            /\ UNCHANGED << chans, parents, start, l, parent, k >>

l3(self) == /\ pc[self] = "l3"
            /\ IF Len(childs[self]) > 0
                  THEN /\ pc' = [pc EXCEPT ![self] = "sendToNeigh"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << chans, parents, start, l, parent, k, childs >>

sendToNeigh(self) == /\ pc[self] = "sendToNeigh"
                     /\ chans' = [chans EXCEPT ![Head(childs[self])] = Append((chans[Head(childs[self])]),(self+1))]
                     /\ childs' = [childs EXCEPT ![self] = Tail(childs[self])]
                     /\ k' = [k EXCEPT ![self] = k[self] + 1]
                     /\ pc' = [pc EXCEPT ![self] = "l3"]
                     /\ UNCHANGED << parents, start, l, parent >>

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
\* Last modified Fri Jan 16 09:00:19 CET 2015 by remi
\* Created Fri Jan 09 09:00:07 CET 2015 by remi
