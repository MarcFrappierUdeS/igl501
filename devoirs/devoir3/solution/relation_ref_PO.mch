MACHINE relation_ref_PO

CONSTANTS k

PROPERTIES
  k = 2

/* obligation preuve de l'initialisation */

  /* [init']  [init]  J */

& J(((0..k) * (0..k)) * {FALSE},{})

/* Obligation de preuve pour operation ajouter */

  /* quantification universelle sur toutes les variables de la machine, du raffinement et les paramètres de l'opération */
& !(f,r,x,y).
  (
    (
      ( 
        I
      & J(f,r)

        /* P */
      & x : 0..k & y : 0..k
      )
    =>
      (
        /* P' */
        x : 0..k & y : 0..k 

      /* [ S' ]  [S]  (J) */
      & J(f <+ {(x,y) |-> TRUE}, r \/ {x |-> y})
      )
    )
  )

/* Obligation de preuve pour operation produit */

  /* quantification universelle sur toutes les variables de la machine, du raffinement et les paramètres de l'opération */
& !(f,r).
  (
    (
      ( 
        I
      & J(f,r)
      )
    =>
      (
      /* [ S' ]  [S]  (J) */
        J(
            {x,y,v |
                x : 0..k
              & y : 0..k
              & v = bool
                  (
                  #z.
                    (
                      z : 0..k
                    & f(x|->z)=TRUE
                    & f(z|->y)=TRUE
                    )
                  )
            }
          ,
            (r;r)
          )
      )
    )
  )
/* Obligation de preuve pour operation appartient */

  /* quantification universelle sur toutes les variables de la machine, du raffinement et les paramètres de l'opération */
& !(f,r,x,y).
  (
    (
      ( 
        I
      & J(f,r)
      )
        /* P */
      & x : 0..k & y : 0..k
    =>
      (
        /* P' */
        x : 0..k & y : 0..k

      /* [ [s := s'] S' ]  [S]  (s=s') */
      & bool(x |-> y : r) = f(x|->y)
      )
    )
  )

DEFINITIONS
 
  J(f,r) ==
    (
      f : ((0..k) * (0..k)) --> BOOL
    & dom(f|>{TRUE}) = r
    )
;
  I ==
    (
    r : 0..k <-> 0..k
    )
END