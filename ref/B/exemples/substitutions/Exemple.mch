MACHINE Exemple

CONSTANTS k

PROPERTIES
  k ∈ NAT

VARIABLES x, v, nbp1, nbp5, nbp10

INVARIANT
  x ∈ NAT
∧ v ∈ 0..k-1 → NAT
∧ nbp1 ∈ NAT
∧ nbp5 ∈ NAT
∧ nbp10 ∈ NAT

DEFINITIONS

nbsuffisantPiece(y1,y5,y10,z1) ==
    (
      y1 ∈ NAT
    ∧ y5 ∈ NAT
    ∧ y10 ∈ NAT
    ∧ z1 = y1 + y5 * 5 + y10 * 10
    ∧ y1 ≤ nbp1
    ∧ y5 ≤ nbp5
    ∧ y10 ≤ nbp10
    )

INITIALISATION
       x := 0
    || v :∈ 0..k-1 → NAT
    || nbp1 := 2
    || nbp5 := 2
    || nbp10 := 2

OPERATIONS

Op1 = CHOICE x:= 1 OR x := -1 END;

Op2 = CHOICE x:= 1 OR x := 2 END;

Op3 = ANY y WHERE y ∈ INT THEN x := y END;

Op4 = ANY y WHERE y > 0 THEN x := y END;

Op5 = SELECT
          x > 0 THEN x := 1
      WHEN
          x = 0 THEN x := -1
      END;

// Recherche position de e dans v; -1 si non présent
i <-- Recherche(e) =
    PRE
	e ∈ NAT
    THEN
      ANY
        i_
      WHERE
          i_ ∈ -1..(k-1)
        ∧ (e ∈ ran(v) ⇒ v(i_) = e & i_ ∈ 0..k-1)
        ∧ (e ∉ ran(v) ⇒ i_ = -1)
      THEN
        i := i_
      END
    END;

// Vérifie si w est trié
b <-- Trie(w) =

    PRE
      w ∈ 1..k → NAT
    THEN
      b := bool(∀x.(x ∈ 1..(k-1) ⇒ w(x) ≤ w(x+1)))
    END;

// retourne un nombre de pièces dont le total est z
p1, p5, p10 <-- Monnaie(z) =
    PRE 
        z ∈ 0..15
    THEN
        ANY wp1, wp5, wp10
        WHERE
             wp1 ∈ NAT
           ∧ wp5 ∈ NAT
           ∧ wp10 ∈ NAT
           ∧ z = wp1 + wp5 * 5 + wp10 * 10
        THEN
              p1 := wp1
           || p5 := wp5
           || p10 := wp10
       END
    END;

p1, p5, p10 <-- MonnaieBis(z) =
    PRE
           z ∈ 0..45
         ∧ ∃(y1,y5,y10).(nbsuffisantPiece(y1,y5,y10,z))
    THEN
        ANY wp1, wp5, wp10 WHERE
          nbsuffisantPiece(wp1,wp5,wp10,z)
       THEN
          p1 := wp1
       || p5 := wp5
       || p10 := wp10
       END
    END;

s <-- Somme = s := SIGMA(z).(z ∈ 0..k-1 | v(z))        
    
END


