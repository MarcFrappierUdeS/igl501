MACHINE Q1_ref_PO
CONSTANTS T,U,k
PROPERTIES k = 2 & T = 1..k & U = 1..(k*k)

/* obligation preuve de l'initialisation */

  /* [init']  [init]  J */

& J((T*T)*{FALSE},U*{FALSE})

  /* Obligation de preuve pour operation set */

  /* quantification universelle sur toutes les variables de la machine, du raffinement et les paramètres de l'opération */
& !(f,v,x,y,b).
  (
    (
      ( 
        I
      & J(v,f)

        /* P */
      & x : T
      & y : T
      & b : BOOL
      )
    =>
      (
        /* P' */
        x : T
      & y : T
      & b : BOOL

      /* [ S' ]  [S]  (J) */
      & J(v <+ {(x,y) |-> b},f <+ {(x-1)*k+y |-> b})
      )
    )
  )

  /* Obligation de preuve pour operation flip */

  /* quantification universelle sur toutes les variables de la machine, du raffinement et les paramètres de l'opération */
& !(f,v,x,y).
  (
    (
      ( 
        I
      & J(v,f)

        /* P */
      & x : T
      & y : T
      )
    =>
      (
        /* P' */
        x : T
      & y : T
      /* [ S' ]  [S]  (J) */
      & 
        (
          f((x-1)*k+y) = TRUE
        =>
          J(v <+ {(x,y) |-> FALSE},f <+ {(x-1)*k+y |-> FALSE})
        )
      & 
        (
          f((x-1)*k+y) = FALSE
        =>
          J(v <+ {(x,y) |-> TRUE},f <+ {(x-1)*k+y |-> TRUE})
        )
      )
    )
  )

  /* Obligation de preuve pour operation get */

  /* quantification universelle sur toutes les variables de la machine, du raffinement et les paramètres de l'opération */
& !(f,v,x,y).
  (
    (
      ( 
        I
      & J(v,f)

        /* P */
      & x : T
      & y : T
      )
    =>
      (
        /* P' */
        x : T
      & y : T
      /* [ S' ]  [S]  (s' = s) */
      & 
        f((x-1)*k+y) = v(x,y)
      )
    )
  )

DEFINITIONS
 
  J(v,f) ==
    (
      f : U --> BOOL
    & !(x1,y1).
        (
              x1 : T
            & y1 : T
        =>
            f((x1-1)*k+y1) = v(x1,y1)
        )
    )
  ;
  I ==
    (
    v : (T*T) --> BOOL
    )
END