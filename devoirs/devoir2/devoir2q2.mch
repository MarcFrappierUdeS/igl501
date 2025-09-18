MACHINE devoir2q2
 
DEFINITIONS
   fc(x,y,u) ==    // u est un facteur commun de x et y
      (
        u : 1..min({x,y})
      & x mod u = 0
      & y mod u = 0
      )
// préférences d'animation de ProB
;   SET_PREF_MAXINT == 5
;   SET_PREF_MININT == -5
;   SET_PREF_MAX_OPERATIONS == 10  // Nombre maximale de enabled operations calculées

CONSTANTS n
PROPERTIES n = 4

VARIABLES x1, x2
INVARIANT
    x1 : NAT
  & x2 : NAT

INITIALISATION

x1,x2 := 1,2

OPERATIONS

  permuter =

  // à compléter

;
  z <-- pgfc(x,y) =

  PRE
      x : {48,10}
    & y : {60,11}
  THEN
  // à compléter
  END
;	
  z <-- loterie(x) =

  PRE
      x : 1..4
  THEN
  // à compléter
  END
;
  i,m <-- minimum(v) = 

  PRE
    v : 1..n --> NAT
  THEN
  // à compléter
  END
;
  v2 <-- trier(v1) =

  PRE
    v1 : 1..n --> NAT
  THEN
    // à compléter
  END
END