MACHINE Map(cap)

CONSTRAINTS
  cap : NAT

SETS K={k1,k2,k3}; V={v1,v2,NULL} /* valeur pour animer votre specification */

VARIABLES map

INVARIANT
  map ∈ K ⇸ V

INITIALISATION map := ∅

OPERATIONS

  previous_value <-- put(key, value) =
    PRE 
        key ∈ K 
      ∧ value ∈ V
      & card(map) < cap
    THEN 
          IF 
            key ∈ dom(map) 
          THEN 
            previous_value := map(key) 
          ELSE 
            previous_value := NULL 
          END
      ||
          map(key) := value    
    END
;
  hasKey <-- containsKey(key) =
    PRE
      key ∈ K
    THEN
      hasKey := bool(key ∈ dom(map))
    END
;
  hasValue <-- containsValue(value) =
    PRE
      value ∈ V
    THEN
      hasValue := bool(value ∈ ran(map))
    END
;
  value <-- get(key) =
    PRE
      key ∈ K
    THEN
      IF 
          key ∈ dom(map) 
      THEN 
          value := map(key) 
      ELSE 
          value := NULL 
      END
    END
;
  empty <-- isEmpty =
    empty := bool(map = ∅)
;
  value <-- remove(key) =
    PRE 
      key ∈ K
    THEN 
      IF 
          key ∈ dom(map) 
      THEN 
          value := map(key) ||
          map := {key} ⩤ map
      ELSE 
          value := NULL 
      END
    END        
END
