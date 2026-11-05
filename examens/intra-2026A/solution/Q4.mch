MACHINE Q4
SETS	

  VA = {v1,v2,v3,v4}  // Dénote l'ensemble des valeurs possibles pour les sommets

VARIABLES V,E

INVARIANT
  V <: VA
& E <: POW(V)

INITIALISATION
   V := {}
|| E := {}

OPERATIONS

AjoutSommet(v) =

PRE
    v : VA
  & v /: V
THEN
  V := V \/ {v}
END;

r <-- AjoutArete(S) =

PRE
  S <: V
THEN
      E := E \/ {S}
  ||  r := bool(S : E)
END;

SupSommet(v) =

PRE
    v : VA
  & not(#S.(S : E & v : S))
THEN
  V := V - {v}
END;

SupSommetArete(v) =

PRE
  v : VA
THEN
      V := V - {v}
  ||  E := { S | S : E & v /: S }
END;

r <-- Chemin(s1, s2, t1, t2) =
PRE
    s1 : seq(V) 
  & s2 : seq(POW(VA))
  & s1 /= [] & s2 /= []
  & card(s1) = card(s2)+1 
  & t1 : V
  & t2 : V
THEN
  r := bool(t1 = first(s1) & t2 = last(s1) &
            !i.(i : dom(s2) => s1(i) : s2(i) & s1(i+1) : s2(i)))
END
END




