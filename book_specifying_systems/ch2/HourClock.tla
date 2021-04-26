----------------------------- MODULE HourClock -----------------------------

EXTENDS Naturals
VARIABLE hr

HCini == hr \in (1..12)

HCnext1 == hr' = IF hr # 12 THEN hr + 1 ELSE 1
HCSpec1 == HCini /\ [][HCnext1]_hr

HCnext2 == hr' = (hr % 12) + 1
HCSpec2 == HCini /\ [][HCnext1]_hr

-----------------------------------------------------------------------------

THEOREM HCSpec1 \/ HCSpec2 => []HCini 

=============================================================================
