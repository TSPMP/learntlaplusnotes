-------------------------- MODULE Channel -----------------------------------

EXTENDS Naturals
CONSTANT Data
VARIABLE chan
TypeInvariant == chan \in [val: Data, rdy: {0, 1}, ack: {0, 1}]

-----------------------------------------------------------------------------

Init == /\ TypeInvariant
        /\ chan.rdy = chan.ack
(* Depending Send on the actual data value makes it easier for other specs *)
(* to additionally specify conditions/transformations based on the actual *)
(* value. *)
Send(d) == /\ chan.rdy = chan.ack
           /\ chan' = [chan EXCEPT !.val = d, !.rdy = 1 - @]
Rcv == /\ chan.rdy # chan.ack
       /\ chan' = [chan EXCEPT !.ack = chan.rdy]
Next == (\E d \in Data: Send(d)) \/ Rcv
Spec == Init /\ [][Next]_chan

-----------------------------------------------------------------------------

THEOREM Spec => [] TypeInvariant

=============================================================================
