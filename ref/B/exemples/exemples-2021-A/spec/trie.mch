MACHINE trie

CONSTANTS v1,v2,k,f
PROPERTIES
  v1 : 1..k --> NAT
& v1 = {(1,2),(2,1),(3,2),(4,1)}
& v2 : 1..k --> NAT
& !(i,j).(i : 1..k & j : 1..k & i < j => v2(i) <= v2(j))
& f : 1..k >-> 1..k
& v2 = (f;v1)
& k = 4
END

