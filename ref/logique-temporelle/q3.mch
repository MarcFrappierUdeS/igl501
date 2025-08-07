MACHINE M

DEFINITIONS

  ASSERT_LTL0 == "GF [b]"
; ASSERT_LTL1 == "G ([a] U [b])"
; ASSERT_LTL2 == "G [a]" // faux
; ASSERT_LTL3 == "G ([b] U [a])"

VARIABLES s,x

INVARIANT
  s ∈ 0..1
& x ∈ NAT
INITIALIZATION
   s := 0
|| x :∈ NAT

OPERATIONS

a =
PRE s = 0
THEN
  IF x > 0 THEN x := x−1
  ELSE s := 1 END
END
;
b =
PRE
  s = 1
THEN
    s := 0
||  x :∈ NAT
END
;
c =
PRE
  s = 0
THEN
  x :∈ NAT
END
END
