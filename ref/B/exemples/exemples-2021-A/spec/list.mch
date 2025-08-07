MACHINE List(k)

CONSTRAINTS
  k : NAT

SETS
 E={e1,e2}

VARIABLES f

INVARIANT
    f : 0..(k-1) +-> E
  & dom(f) = 0..(card(f)-1) // elements contigus et débute à 0

INITIALISATION
  f := {}

OPERATIONS

b <-- Add(e) =
  PRE
      e : E
    & card(f) < k
  THEN
       f(card(f)) := e
    || b := TRUE
  END;

AddP(i,e)=
  PRE
      i >= 0
    & i<= card(f)
    & card(f) < k
  THEN
    f :=    (0..(i-1)) <| f
         \/ {(i,e)}
         \/ (succ~ ; (i..(card(f)-1)) <| f)
  END
;
Remove(i) =
  PRE
      i >= 0
    & i < card(f)
  THEN
    f :=    (0..(i-1)) <| f
         \/ (succ ; ((i+1)..(card(f)-1)) <| f)
  END
;
S <-- ToSet =
  S := ran(f)
;
C <-- ToCollection =
  C := %x.(x : ran(f) | card(f |> {x}))  
END