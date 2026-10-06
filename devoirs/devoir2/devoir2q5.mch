MACHINE Map(cap)
 
CONSTRAINTS
  cap : NAT

SETS
  K={k1,k2,k3} /* ensemble des cles */
;
  V={v1,v2,NULL} /* ensemble des valeurs */

VARIABLES map

INVARIANT
...

INITIALISATION ...

OPERATIONS

  previous_value <-- put(key, value) =
    PRE 
        key ∈ K 
      ∧ value ∈ V
      ...
    THEN
      ...
;
  hasKey <-- containsKey(key) =
    PRE
      key ∈ K
    THEN
    ...
;
  hasValue <-- containsValue(value) =
    ...
;
  value <-- get(key) =
    PRE
      key ∈ K
    THEN
      ...
;
  empty <-- isEmpty =
    empty := bool(map = ∅)
;
  value <-- remove(key) =
    PRE 
      key ∈ K
    THEN 
      ...
    END        
END
