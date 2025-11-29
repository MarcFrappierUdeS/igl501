MACHINE file_ref_PO
CONSTANTS k
PROPERTIES

/* obligation preuve de l'initialisation */

  /* [init'] not [init] not J */
  k = 3
& ((0..(k-1)) * {0}) : 0..(k-1) --> 0..k
& 0 : 0..(k-1)
& 0 : 0..k
& 0 = size([])
& !(x).
    (
      x : dom([])
    =>
      [](x) = ((0..(k-1)) * {0})((0 + x - 1) mod k)
    )

/* obligation de preuve de tete */		
&
  /* quantification universelle sur toutes les variables de la machine et du raffinement */
  !(f,v, d, n).
  (
    (
      ( /* I */
        f : seq(0..k)
      & size(f) <= k
        /* J */
      & v : 0..(k-1) --> 0..k
      & d : 0..(k-1)
      & n : 0..k
      & n = size(f)
      & !(x).
          (
            x : dom(f)
          =>
            f(x) = v((d + x - 1) mod k)
          )
        /* P */
      & size(f) > 0
      )
    =>
      (
        /* P' */
        n > 0
        /* [ [s := s'] S' ] not [S] not (J & s = s' ) */
      & v(d) = first(f)
      )
    )
  )
/* obligation de preuve de enfiler */
  /* quantification universelle sur toutes les variables de la machine, du raffinement et les paramètres de l'opération */
& !(f,v, d, n, x).
  (
    (
      ( /* I */
        f : seq(0..k)
      & size(f) <= k
        /* J */
      & v : 0..(k-1) --> 0..k
      & d : 0..(k-1)
      & n : 0..k
      & n = size(f)
      & !(x).
          (
            x : dom(f)
          =>
            f(x) = v((d + x - 1) mod k)
          )
        /* P */
      & x : 0..k & size(f) < k
      )
    =>
      (
      /* P' */
        x : 0..k & n < k
      /* [ S' ] not [S] not (J) */
      & v <+ {((d+n) mod k) |-> x } : 0..(k-1) --> 0..k
      & d : 0..(k-1)
      & n+1 : 0..k
      & n+1 = size(f <- x)
      & !(y).
          (
            y : dom(f)
          =>
            (f <- x)(y) = (v <+ {((d+n) mod k) |-> x })((d + y - 1) mod k)
          )
      )
    )
  )
/* obligation de preuve de defiler */
  /* quantification universelle sur toutes les variables de la machine, du raffinement et les paramètres de l'opération */
& !(f,v, d, n).
  (
    (
      ( /* I */
        f : seq(0..k)
      & size(f) <= k
        /* J */
      & v : 0..(k-1) --> 0..k
      & d : 0..(k-1)
      & n : 0..k
      & n = size(f)
      & !(x).
          (
            x : dom(f)
          =>
            f(x) = v((d + x - 1) mod k)
          )
        /* P */
      & size(f) > 0
      )
    =>
      (
      /* P' */
        n > 0
      /* [ S' ] not [S] not (J) */
      & v : 0..(k-1) --> 0..k
      & ((d+1) mod k) : 0..(k-1)
      & (n-1) : 0..k
      & (n-1) = size(tail(f))
      & !(y).
          (
            y : dom((tail(f)))
          =>
            (tail(f))(y) = v((((d+1) mod k) + y - 1) mod k)
          )
      )
    )
  )


END