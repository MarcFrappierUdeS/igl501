MACHINE q3

CONSTANTS k

PROPERTIES
  k ∈ NAT
∧ k = 3

VARIABLES l

INVARIANT
  l ∈ iseq(NAT)
∧ size(l) ≤ k

INITIALISATION l := []

OPERATIONS

add(x) =
PRE
   x ∈ NAT
∧  x ∉ ran(l)
∧  size(l) < k
THEN
  l := l <- x
END;

addp(x,p) =
PRE
  x ∈ NAT
∧ x ∉ ran(l)
∧ p ∈ 1..size(l)+1
∧ size(l) < k
THEN
  l := ((1..(p-1) ◁ l) ^ [x]) ∪ (succ⁻¹;(p..size(l) ◁ l))
END;

del(x) =
PRE
  x ∈ NAT
THEN
  IF x ∈ ran(l)
  THEN
    ANY i WHERE l(i) = x THEN  l := (1..(i-1) ◁ l) ∪ (succ;((i+1)..size(l) ◁ l)) END
  END
END;

delp(p) =
PRE
  p ∈ 1..size(l)
THEN
  l := (1..(p-1) ◁ l) ∪ (succ;((p+1)..size(l) ◁ l))
END;

sort =
ANY m,l2
WHERE
   m ∈ 1..size(l) >->> 1..size(l)
∧ l2 = (m;l)
∧ ∀(i).(i ∈ 1..size(l)-1 ⇒ l2(i) ≤ l2(i+1))
THEN
  l := l2
END

END


