MACHINE Somme

CONSTANTS k

PROPERTIES k = 3

OPERATIONS

r <-- somme(v) =

PRE
  v : 1..k --> NAT
THEN
  r := SIGMA(z).(z : 1..k | v(z))
END

END