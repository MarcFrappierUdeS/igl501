MACHINE relation(k)
CONSTRAINTS k : NAT & k = 2
VARIABLES r
INVARIANT r : 0..k <-> 0..k
INITIALISATION r := {}
OPERATIONS

ajouter(x, y) =
PRE x : 0..k & y : 0..k
THEN r := r \/ {x |-> y}
END;

produit = BEGIN r := (r;r) END;

res <-- appartient(x, y) =
PRE x : 0..k & y : 0..k
THEN res := bool(x |-> y : r)
END

END
