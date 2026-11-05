MACHINE Q5
SETS	

  VA = {v1,v2,v3,v4}  // Dénote l'ensemble des valeurs possibles pour les sommets

CONSTANTS m, VB

PROPERTIES m : NAT & VB <: VA

VARIABLES V,E

INVARIANT
  V <: VA
& E <: POW(V)
/* 5a */
& !v.(v : V => card({e | e : E & v : e}) <= m)
/* 5b */
& !(vb1,vb2).(vb1 : VB & vb2 : VB & vb1 /= vb2 => not(#e.(e : E & {vb1,vb2} <: e)))
/* 5c */
& closure1({s1,s2 | s1 : V & s2 : V & s1 /= s2 & #(e).(e : E & {s1,s2} <: e)}) /\ id(V) = {}

INITIALISATION
   V := {}
|| E := {}

OPERATIONS
op = skip

END




