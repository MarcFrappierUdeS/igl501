MACHINE Devoir1Partie2
SETS
    Livre = {li1,li2,li3}
;   Membre = {me1,me2,me3}

CONSTANTS pret, reservation, Q1, Q2, Q3, Q4, Q5, Q6, Q7, Q8, Q9, k

PROPERTIES
    pret : Livre +-> Membre
&   !m.(m : Membre => card(pret |> {m}) <= k)
&   k = 3
&   pret = {(li1,me1),(li2,me1)}
&   reservation : Livre <-> Membre
&   reservation = { (li1,me2), (li1,me3), (li3,me1) }
&   Q1 = { m1,m2 | #l.((l,m1) : reservation & (l,m2) : reservation) }
&   Q2 = (reservation~ ; reservation) - id(Membre)
&   Q3 = { m | #l.(l : Livre & ((l,m) : pret or (l,m) : reservation)) }
&   Q4 = ran(pret) \/ ran(reservation)
&   Q5 = { m,n | m : Membre & n = card(pret~[{m}])}
&   #n.(n : NAT & n = max(ran(Q5)) & (Q6,n) : Q5)
&   Q7 = { x | x <: Livre & #m.(m : Membre & x = pret~[{m}]) }
&   Q8 = ( pret~ ; reservation )
&   Q9 = bool(dom(reservation) <: dom(pret))
END

