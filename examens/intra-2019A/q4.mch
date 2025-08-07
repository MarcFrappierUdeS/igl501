MACHINE q4
SETS
  R={r1,r2}
; U={u1,u2}

VARIABLES demande, allocation

INVARIANT
   demande : R --> iseq(U)
&  allocation <: R

INITIALISATION
    demande := R*{[]}
||  allocation := {}

OPERATIONS

demander(u,r) =
PRE
    u : U
  & r : R
  & u /: ran(demande(r))
THEN
  demande(r) := demande(r) <- u 
END;

allouer(r) = 
PRE
    r /: allocation
  & demande(r) /= []
THEN
      allocation := allocation \/ {r} 
  ||  demande(r) := tail(demande(r))
END;

liberer(r) =
PRE
  r : allocation
THEN
  allocation := allocation - {r}
END

END

