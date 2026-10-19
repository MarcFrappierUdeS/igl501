MACHINE devoir_p1_q2_a

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

  x1 := x2 || x2 := x1

;

  z <-- pgfc(x,y) =

  PRE
      x : {48,10}
    & y : {60,11}
  THEN
      ANY
          u
      WHERE
          fc(x,y,u)
        & !(u2).(u2 /= u & fc(x,y,u2) => u2 < u)
      THEN
          z := u
      END
  END

;

  z <-- loterie(x) =

  PRE
      x : 1..4
  THEN
      SELECT
          x : 1..2 THEN z := 2*x
      WHEN
          x : 2..3 THEN z := 3*x
      WHEN
          x : 3..4 THEN z := 4*x
      END
  END
;
  i,m <-- minimum(v) = 

  PRE
        v : 1..n --> NAT
  THEN
    ANY i_ WHERE
        i_ : 1..n
      & !x.(x : 1..n => v(x) >= v(i_))
    THEN
          i := i_
      ||  m := v(i_)
    END
  END
;
  v3 <-- somme(v1,v2) =

  PRE
      v1 : 1..n --> NAT
    & v1 : 1..n --> NAT

  THEN
      ANY w
      WHERE
          w : 1..n --> 1..n  //
        & !i.( i : 1..n => w(i) = v1(i)+v2(i) )  
      THEN
          v3 := w
      END
  END
;

  v2 <-- trierBis(v1) =

  PRE
      v1 : 1..n --> NAT
  THEN
      ANY v
      WHERE 
          v : 1..n --> ran(v1)
          & !y.(y:ran(v1)=>card(v~[{y}])=card(v1~[{y}]))
          & !i.(i:1..(n-1)=>v(i)<=v(i+1))
      THEN
          v2 := v
      END
  END

END