MACHINE Somme_imp_PO

DEFINITIONS
 
  I(r,i) ==
    (
    r = SIGMA(z).(z : 1..i | v(z)) & i ∈ 0..k
    )
;
  C == (i < k)

CONSTANTS k

PROPERTIES
  k = 3

/*
   Soit S' = Init;W, où Init est l'initialisation de la boucle et W est la boucle While, ie,
        W = WHILE C DO B INVARIANT I VARIANT V END
        Init = r := 0; i := 0;

   Soit S = r := SIGMA(z).(z : 1..k | v(z))
*/

/* Obligations de preuve pour operation somme */

  /* Obligation de preuve pour que la boucle établisse s = s' */
  /* quantification universelle sur les paramètres de l'opération */
& !(v).
  (
    (
      ( 
        /* P */
      v : 1..k --> NAT
      )
    =>
      (

/* W1 ∀ X · (I ∧ C ⇒ [B]I) */
        !(r,i).
          (
              r : 0..k /* *** ajouté pour limiter la vérificatin à cet intervalle pour la sortie r */
            & I(r,i) & C
          =>
            I(r + v(i+1),i+1)
          )

/* (W2) ∀ X · (I ⇒ V ∈ N) */
      & !(r,i).
          (
              r : 0..k /* *** ajouté pour limiter la vérificatin à cet intervalle pour la sortie r */
            & I(r,i)
          =>
            k-i >= 0
          )

/* (W3) ∀ X · (I ∧ C ⇒ [n := V ; B](V < n)) */
      & !(r,i).
          (
              r : 0..k /* *** ajouté pour limiter la vérificatin à cet intervalle pour la sortie r */
            & I(r,i)
            & C
          =>
            k-(i+1) < k-i
          )

/* (W4) ∀ X · (I ∧ ¬C ⇒ r1 = r) */
        /* on utilise r1 au lieu r, car on doit renommer la variable de sortie dans la machine concrète, car elle porte le même nom dans la machine abstraite  */
      & !(r1,i).
          (
              r1 : 0..k /* *** ajouté pour limiter la vérificatin à cet intervalle pour la sortie r */
            & I(r1,i)
            & not (C)
          =>
            r1 = SIGMA(z).(z : 1..k | v(z))
          )

/* Obligation de preuve que l'initialisation établit l'invariant */
      & I(0,0)

      )
    )
  )


END