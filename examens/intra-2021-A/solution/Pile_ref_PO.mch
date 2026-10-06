MACHINE Pile_ref_PO
CONSTANTS k
PROPERTIES
  k : NAT
& k = 3

  /* Obligation de preuve pour init */

&  J((1..k ) * {0},0,{})

  /* Obligation de preuve pour Push */

& !(e,v,t,p).
    (
        I(p)
      & J(v,t,p)
      & e : NAT & card(p) < k
    =>
        e : NAT & t < k
      & J(v <+ {(t+1,e)}, t+1, p <+ {(card(p)+1,e)})
    )

  /* Obligation de preuve pour Pop */

& !(v,t,p).
    (
        I(p)
      & J(v,t,p)
      & card(p) > 0 
    =>
        t > 0
      & J(v, t-1, 1..(card(p)-1) <| p)
    )

  /* Obligation de preuve pour Top */

& !(v,t,p).
    (
        I(p)
      & J(v,t,p)
      & card(p) > 0 
    =>
        t > 0
      & v(t) = p(card(p))
    )

  /* Obligation de preuve pour Max */

& !(v,t,p).
    (
        I(p)
      & J(v,t,p)
      & card(p) > 0 
    =>
        t > 0
      & max(ran(1..t <| v)) = max(ran(p))
    )

 /* Obligation de preuve pour sort */

&  !(v,t,p).
    (
        I(p)
      & J(v,t,p)
    =>
        (
        !v1.
          (
            (
              v1 : 1..k +-> NAT
            & #f.(
                   f : 1..t >-> 1..t
                 & v1 = (f;v) \/ (id((t+1)..k) ; v)
                 & !(i,j).(i : 1..t & j : 1..t & i < j => v1(i) <= v1(j))
                 )
            )
          =>
            not(
              !p1.
                (
                  (
                    p1 : 1..k +-> NAT
                  & #f.(
                         f : dom(p) >-> dom(p)
                       & p1 = (f;p)
                       & !(i,j).(i : dom(p) & j : dom(p) & i < j => p1(i) <= p1(j))
                       )
                  )
                =>
                  not (J(v1,t,p1))
                )
              )
          )
        )
    )

DEFINITIONS

  J(v,t,p) ==
    (
      v : 1..k --> NAT
    & t : 0..k
    & p = 1..t <| v
    )
;
  I(p) ==
    (
      p : 1..k +-> NAT
    & dom(p) = 1..card(p)
    & card(p) <= k
    )
END
