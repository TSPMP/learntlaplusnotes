--------------------------- MODULE InternalMemory ---------------------------

EXTENDS MemoryInterface
VARIABLES mem, ctl, buf

-----------------------------------------------------------------------------

(* The initial predicate *)
IInit ==
    (* Initially, memory locations have any values in Val *)
    /\ mem \in [Adr -> Val]
    (* each processor is ready to issue requests *)
    /\ ctl = [p \in Proc |-> "rdy"]
    (* each buf is arbitrarily initialized to NoVal *)
    /\ buf = [p \in Proc |-> NoVal]
    (* memInt is any element of InitMemInt *)
    /\ memInt \in InitMemInt

(* The type-correctness invariant. *)
TypeInvariant ==
    (* mem is a function from Adr to Val. *)
    /\ mem \in [Adr -> Val]
    (* ctl[p] equals "rdy", "busy", or "done". *)
    /\ ctl \in [Proc -> {"rdy", "busy", "done"}]
    (* buf[p] is a request or response *)
    /\ buf \in [Proc -> MReq \cup Val \cup {NoVal}]

(* Processor p issues a request *)
Req(p) ==
    (* Enabled iff p is ready to issue a request *)
    /\ ctl[p] = "rdy"
    (* For some request req *)
    /\ \E req \in MReq:
        (* Send req on the interface *)
        /\ Send(p, req, memInt, memInt')
        (* Set buf[p] to the request *)
        /\ buf' = [buf EXCEPT ![p] = req]
        (* Set ctl[p] to "busy" *)
        /\ ctl' = [ctl EXCEPT ![p] = "busy"]
    /\ UNCHANGED mem

(* Perform p's request to memory. *)
Do(p) ==
    (* Enabled iff p's request is pending. *)
    /\ ctl[p] = "busy"
    /\ mem' = IF buf[p].op = "Wr"
                (* Write to memory on a "Wr" request *)
                THEN [mem EXCEPT ![buf[p].adr] = buf[p].val]
                (* Leave mem unchanged on a "Rd" request *)
                ELSE mem
    (* Set buf[p] to the response *)
    /\ buf' = [buf EXCEPT ![p] = IF buf[p].op = "Wr"
                (* NoVal for a write *)
                THEN NoVal
                (* the memory value for a read *)
                ELSE mem[buf[p].adr]]
    /\ ctl' = [ctl EXCEPT ![p] = "done"]
    /\ UNCHANGED memInt
    
(* Return the response to p's request. *)
Rsp(p) ==
    (* Enabled iff req done but resp not sent. *)
    /\ ctl[p] = "done"
    (* Send the response on the interface *)
    /\ Reply(p, buf[p], memInt, memInt')
    /\ ctl' = [ctl EXCEPT ![p] = "rdy"]
    /\ UNCHANGED <<mem, buf>>

(* The next-state action *)
INext == \E p \in Proc: Req(p) \/ Do(p) \/ Rsp(p)

(* The specification *)
ISpec == IInit /\ [][INext]_<<memInt, mem, ctl, buf>>

-----------------------------------------------------------------------------

THEOREM ISpec => []TypeInvariant

=============================================================================
