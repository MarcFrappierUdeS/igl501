MACHINE file

CONSTANTS k

PROPERTIES
 k : NAT

VARIABLES f

INVARIANT f : seq(NAT) & size(f) <= k

INITIALISATION f := []

OPERATIONS

enfiler(x) = 
  PRE
      x : NAT
    & size(f) < k
  THEN
    f := f <- x    
  END
;
defiler =
  PRE
    size(f) > 0
  THEN
    f := tail(f)    
  END
;
x <-- tete = 
  PRE
    size(f) > 0
  THEN
    x := first(f)
  END
;
sup(i) =
  PRE
    i : dom(f)
  THEN
      f :=      (1..(i-1)) <| f
            \/  (succ ; (((i+1)..size(f)) <| f))
  END
;
sup_e(x) =
  PRE
    x : NAT
  THEN
    IF
      x : ran(f)
    THEN
      ANY j
      WHERE j : dom(f) & f(j) = x
      THEN
        f :=      (1..(j-1)) <| f
              \/  (succ ; (((j+1)..size(f)) <| f))
      END
    END
  END
;
trier =
    ANY g,h
    WHERE
        h : dom(f) >-> dom(f)
      & g = (h ; f)
      & !i.(i : 1..(size(f)-1) => g(i) <= g(i+1))
    THEN
      f := g
    END

END

