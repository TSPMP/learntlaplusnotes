-------------------------- MODULE MemoryInterface --------------------------

VARIABLE memInt
CONSTANTS
(* A Send(p, r, memInt, memInt') step represents processor p sending *)
(* request r to processor p. Returns TRUE iff a step in which memInt' *)
(* represents the state after sending request r by p of to the memory *)
Send(_, _, _, _),
(* A Reply(p, d, memInt, memInt') step represents the memory sending value *)
(* d to processor p *)
Reply(_, _, _, _),
(* The set of possible initial values of memInt *)
InitMemInt,
(* The set of processor identifiers *)
Proc,
(* The set of memory addresses *)
Adr,
(* The set of memory values *)
Val

ASSUME \A p, d, miOld, miNew: /\ Send(p, d, miOld, miNew) \in BOOLEAN
                              /\ Reply(p, d, miOld, miNew) \in BOOLEAN
                              
-----------------------------------------------------------------------------

(* The set of all requests; a read specifies an address, a write specifies *)
(* an address and a value *)
MReq == [op: {"Rd"}, adr: Adr] \cup [op: {"Wr"}, adr: Adr, val: Val]
(* An arbitrary value not in Val *)
NoVal == CHOOSE v: v \notin Val

=============================================================================
