MACHINE Pile

CONSTANTS k
PROPERTIES
  k : NAT
& k = 3
VARIABLES p
INVARIANT
  p : 1..k +-> NAT
& dom(p) = 1..card(p)
& card(p) <= k

INITIALISATION p := {}
OPERATIONS
  Push(e) = PRE e : NAT & card(p) < k THEN p(card(p)+1) := e END
; Pop = PRE card(p) > 0 THEN p := 1..(card(p)-1) <| p END
; e <-- Top = PRE card(p) > 0 THEN e := p(card(p)) END
; Sort =
    ANY p1
    WHERE
        p1 : 1..k +-> NAT
      & #f.(
             f : dom(p) >-> dom(p)
           & p1 = (f;p)
           & !(i,j).(i : dom(p) & j : dom(p) & i < j => p1(i) <= p1(j))
           )
    THEN p := p1
    END
;  e <-- Max = PRE card(p) > 0 THEN e := max(ran(p)) END
END









