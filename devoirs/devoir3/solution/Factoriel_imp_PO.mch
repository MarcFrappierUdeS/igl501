MACHINE Factoriel_imp_PO

CONSTANTS k

PROPERTIES
  k = 3


/* Obligation de preuve pour operation factoriel */

  /* Obligation de preuve pour que la boucle établisse s = s' */
  /* quantification universelle sur les paramètres de l'opération */
& !(n).
  (
    (
      ( 
        /* P */
      n : 0..k
      )
    =>
      (
        /* P' */
        n : 0..k

      /* [ [s := s'] S' ]  [S]  (s=s') */

/* W1 ∀ X · (I ∧ C ⇒ [S]I) */
      & !(r,i).
          (
              r : 0..(PI(z).(z : 1..k | z))
            & I(r,i) & C
          =>
            I(r*(i+1),i+1)
          )

/* (W2) ∀ X · (I ⇒ V ∈ N) */
      & !(r,i).
          (
              r : 0..(PI(z).(z : 1..k | z))
            & I(r,i)
          =>
            n-i >= 0
          )

/* (W3) ∀ X · (I ∧ C ⇒ [n := V ; S](V < n)) */
      & !(r,i).
          (
              r : 0..(PI(z).(z : 1..k | z))
            & I(r,i)
            & C
          =>
            n-(i+1) < n-i
          )

/* (W4) ∀ X · (I ∧ ¬C ⇒ s' = s) */
        /* renommage de r en r1 pour éviter collision avec r de machine abstraite */
      & !(r1,i).
          (
              r1 : 0..(PI(z).(z : 1..k | z))
            & I(r1,i)
            & not (C)
          =>
            r1 = PI(z).(z : 1..n | z)
          )

/* Obligation de preuve que l'ínitialisation établit l'invariant */
      & I(1,0)
      )
    )
  )

DEFINITIONS
 
  I(r,i) ==
    (
    r = PI(z).(z : 1..i | z) & i ∈ 0..n
    )
;
  C == (i < n)
END