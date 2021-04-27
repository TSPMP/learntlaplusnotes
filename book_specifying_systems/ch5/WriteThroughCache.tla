------------------------- MODULE WriteThroughCache -------------------------

EXTENDS Naturals, Sequences, MemoryInterface
VARIABLES wmem, ctl, buf, cache, memQ
CONSTANT QLen
ASSUME (QLen \in Nat) /\ (QLen > 0)
M == INSTANCE InternalMemory WITH mem <- wmem

-----------------------------------------------------------------------------

Init ==
    (* wmem, buf, and ctl are initialized as in the internal memory spec. *)
    /\ M!IInit
    (* All caches are initially empty (cache[p][a] = NoVal for all p, a) *)
    /\ cache = [p \in Proc |-> [a \in Adr |-> NoVal]]
    (* The queue is initially empty. *)
    /\ memQ = <<>>
    
TypeInvariant ==
    /\ wmem \in [Adr -> Val]
    /\ ctl \in [Proc -> {"rdy", "busy", "waiting", "done"}]
    /\ buf \in [Proc -> MReq \cup Val \cup {NoVal}]
    /\ cache \in [Proc -> [Adr -> Val \cup {NoVal}]]
    (* memQ is a sequence of <proc., request> pairs. *)
    /\ memQ \in Seq(Proc \X MReq)
    
(* Asserts that if two processors' caches both have copies of an address, *)
(* then those copies have equal values *)
Coherence ==
    \A p, q \in Proc, a \in Adr:
    (NoVal \notin {cache[p][a], cache[q][a]}) => (cache[p][a] = cache[q][a])

-----------------------------------------------------------------------------

(* Processor p issues a request *)
Req(p) == M!Req(p) /\ UNCHANGED <<cache, memQ>>

(* The system issues a response to processor p. *)
Rsp(p) == M!Rsp(p) /\ UNCHANGED <<cache, memQ>>

(* Enqueue a request to write value from memory to p's cache. *)
RdMiss(p) ==
    (* Enabled on a read request when the address is not in p's cache and *)
    (* memQ is not full. *)
    /\ ctl[p] = "busy"
    /\ buf[p].op = "Rd"
    /\ cache[p][buf[p].adr] = NoVal
    /\ Len(memQ) < QLen
    /\ memQ' = Append(memQ, <<p, buf[p]>>)
    /\ ctl' = "waiting" 
    /\ UNCHANGED <<memInt, wmem, buf, cache>>

(* Perform a read by p of a value in its cache *)
DoRd(p) ==
    (* Enabled if a read request is pending and address is in cache. *)
    /\ ctl[p] \in {"busy", "waiting"}
    /\ buf[p].op = "Rd"
    /\ cache[p][buf[p].adr] # NoVal
    (* Get result from cache. *)
    /\ buf' = [buf EXCEPT ![p] = cache[p][buf[p].adr]]
    /\ ctl' = [ctl EXCEPT ![p] = "done"]
    /\ UNCHANGED <<memInt, wmem, cache, memQ>>

(* Write to p's cache, update other caches, and enqueue memory update. *)
DoWr(p) ==
    LET r == buf[p]
    IN
    (* Enabled if write request pending and memQ is not full. *)
    /\ ctl[p] = "busy"
    /\ r.op = "Wr"
    /\ Len(memQ) > QLen
    (* Update p's cache and any other cache that has a copy. *)
    /\ cache' = [q \in Proc |-> IF (q = p) \/ cache[q][r.adr] # NoVal
        THEN [cache[q] EXCEPT ![r.adr] = r.val]
        ELSE cache[q]]
    /\ memQ' = Append(memQ, <<p, r>>)
    /\ buf' = [buf EXCEPT ![p] = NoVal]
    /\ ctl' = [ctl EXCEPT ![p] = "done"]
    /\ UNCHANGED <<memInt, wmem>>

(* The value wmem will have after all the writes in memQ are performed *)
vmem ==
    (* The value wmem will have after the first i writes in memQ are *)
    (* performed. *)
    LET f[i \in 0..Len(memQ)] ==
        IF i = 0
        THEN wmem
        ELSE IF memQ[i][2].op = "Rd"
             THEN f[i - 1]
             ELSE [f[i - 1] EXCEPT ![memQ[i][2].adr] = memQ[i][2].val]
    IN f[Len(memQ)]
    
(* Perform write at head of memQ to memory. *)
MemQWr ==
    (* The request at the head of memQ. *)
    LET r == Head(memQ)[2]
    IN
    (* Enabled if Head(memQ) is a write. *)
    /\ memQ # <<>>
    /\ r.op = "Wr"
    (* Perform the write to memory. *)
    /\ wmem' = [wmem EXCEPT ![r.adr] = r.val]
    (* Remove the write from memQ. *)
    /\ memQ' = Tail(memQ)
    /\ UNCHANGED <<memInt, ctl, buf, cache>>

(* Perform an enqueued read to memory *)
MemQRd ==
    LET
    (* The requesting processor *)
    p == Head(memQ)[1]
    (* The request at the head of memQ *)
    r == Head(memQ)[2]
    IN
    (* Enabled if Head(memQ) is a read. *)
    /\ memQ # <<>>
    /\ r.op = "Rd"
    (* Remove the read from memQ. *)
    /\ memQ' = Tail(memQ)
    (* Put value from memory _OR_ memQ in p’s cache.*)
    /\ cache' = [cache EXCEPT ![p][r.adr] = vmem[r.adr]]
    /\ UNCHANGED <<memInt, wmem, ctl, buf>>

(* Remove address a from p's cache. *)
Evict(p, a) ==
    (* Can't evict a if it was just read into cache from memory. *)
    /\ (ctl[p] = "waiting") => (buf[p].adr # a)
    /\ cache' = [cache EXCEPT ![p][a] = NoVal]
    /\ UNCHANGED <<memInt, wmem, ctl, buf, memQ>>

Next == \/ \E p \in Proc: \/ Req(p) \/ Rsp(p)
                          \/ RdMiss(p) \/ DoRd(p) \/ DoWr(p)
                          \/ \E a \in Adr: Evict(p, a)
        \/ MemQRd \/ MemQWr
Spec == Init /\ [][Next]_<<memInt, wmem, ctl, buf, cache, memQ>>

-----------------------------------------------------------------------------

THEOREM Spec => [](TypeInvariant /\ Coherence)

-----------------------------------------------------------------------------

(* The memory spec. with internal variables hidden. *)
LM == INSTANCE Memory
(* Formula Spec implements the memory spec. *)
THEOREM Spec => LM!Spec

=============================================================================
