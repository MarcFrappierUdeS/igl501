MACHINE emsemble_ref_PO
SETS
 E={e1,e2,e3}

CONSTANTS k

PROPERTIES
  k = 3

/* obligation preuve de l'initialisation */

  /* [init'] [init]  J */

& J((1..k) * {e1},0,{})

/* Obligation de preuve pour Add */

  /* quantification universelle sur toutes les variables de la machine, du raffinement et les paramètres de l'opération */
& !(v,d,e,x).
  (
    (
      ( 
        I
      & J(v,d,e)

        /* P */
      & x:E & x /: e & card(e) < k
      )
    =>
      (
      /* P' */
        x:E & not (appartient(x)) & d < k

      /* [ S' ] [S] (J) */
      &	J(v <+ {(d+1) |-> x}, d+1, e \/ {x})
      )
    )
  )

/* Obligation de preuve pour Del */

  /* quantification universelle sur toutes les variables de la machine, du raffinement et les paramètres de l'opération */
& !(v,d,e,x).
  (
    (
      ( 
        I
      & J(v,d,e)

        /* P */
      & x:E & x : e
      )
    =>
      (
        /* P' */
        x:E & appartient(x)

      /* [ S' ]  [S]  (J) */
      & !y.
          (
            (y : 1..d & v(y) = x)
          =>
            (
              J(
                    1..(y-1) <| v 
                \/
                    (succ ; ((y+1)..d <| v))
                \/
                    ((d..k) <| v)
              ,
                d-1
              ,
                e - {x}
              )
            )
          )
      )
    )
  )

/* Obligation de preuve pour In */

  /* quantification universelle sur toutes les variables de la machine, du raffinement et les paramètres de l'opération */
& !(v,d,e,x).
  (
    (
      ( 
        I
      & J(v,d,e)

        /* P */
      & x:E
      )
    =>
      (
        /* P' */
        x:E

      /* [ [s := s'] S' ]  [S]  (s = s' ) */
      & bool(x : e) = bool(appartient(x))
      )
    )
  )

DEFINITIONS
 
  appartient(x) == ( #i.(i : 1..d & v(i) = x) )
;
/* Invariant de collage : mettre un paramètre pour chaque variable de la machine raffinement et de la machine abstraite, afin de faciliter le calcul des substitutions dans les obligations de preuve */
  J(v,d,e) ==
    (
      v : 1..k --> E
    & d : 0..k
    & d = card(e) 
    & e = ran((1..d) <| v)
    )
;
// Invariant de la machine abstraite
  I ==
    (
    e <: E
    )
END