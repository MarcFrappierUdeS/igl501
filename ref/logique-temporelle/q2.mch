MACHINE M

DEFINITIONS

  ASSERT_LTLa == "FG [e]"
; ASSERT_LTLb == "[a] & X ([b] & XF [e])"
; ASSERT_CTLbs2 == "EX({s=1} & EX ({s=2} & EF {s=3}))"
; ASSERT_CTLbs3 == "EX({s=1} & EX ({s=2}))"
; ASSERT_LTLc == "¬([a] & X([b] & X([c] & X([d] & X(G[e])))))" // faux, afin de montrer que la trace abcdeeee est possible
; ASSERT_CTLa == "AG ({s=1} => EF {s=3})"
; ASSERT_CTLb == "AG ({s=1} => AF {s=3})"
; ASSERT_CTLc == "AF ({s=3})"
; ASSERT_CTLcs == "AF ({s=3})"
; ASSERT_LTLd == "F ({s=3})"

VARIABLES s

INVARIANT
  s ∈ 0..3

INITIALIZATION
  s := 0

OPERATIONS

a =
  PRE
    s = 0
  THEN
    s := 1
  END
;
b =
  PRE
    s = 1
  THEN
    s := 2
  END
;
c =
  PRE
    s = 2
  THEN
    s := 1
  END
;
d =
  PRE
    s = 1
  THEN
    s := 3
  END
;
e =
  PRE
    s = 3
  THEN
    s := 3
  END
END
