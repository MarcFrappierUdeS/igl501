MACHINE devoir2q4
SETS TRAIN
CONSTANTS max_segment
PROPERTIES
 max_segment ∈ NAT1
VARIABLES Train, TrainPosition, isTrainStationed
INVARIANT
 Train ⊆ TRAIN
∧ TrainPosition ∈ Train --> 1..max_segment
∧ !s.
    (
        s:ran(TrainPosition)
    =>
        card(TrainPosition~[{s}]):1..2
    )
∧ isTrainStationed : Train --> BOOL
∧ !t1,t2.
    (
        (   t1:Train
        ∧   t2:Train
        ∧   t1/=t2
        ∧   TrainPosition(t1)=TrainPosition(t2)
        )
    =>
            isTrainStationed(t1)
        /=  isTrainStationed(t2)
    )

INITIALISATION Train, isTrainStationed, TrainPosition := ∅,∅,∅

OPERATIONS
  ajouter_train(t,s) =
	PRE 
		t ∉ Train 
        ∧ s ∈ 1..max_segment
		∧ TrainPosition~[{s}] <: isTrainStationed~[{TRUE}]
	THEN 
		        Train := Train ∪ {t}
        ||  TrainPosition(t) := s
        ||  isTrainStationed(t) := FALSE		
	END
  ;
  avancer(t) =
	PRE 
		  t ∈ Train 
		∧ TrainPosition(t) < max_segment
    ∧ isTrainStationed(t) = FALSE
		∧ TrainPosition~[{TrainPosition(t)+1}] <: isTrainStationed~[{TRUE}]
	THEN 
		 TrainPosition(t) := TrainPosition(t) + 1
	END
 ;
 stationner(t) =
	PRE 
		  t ∈ Train 
    ∧ isTrainStationed(t) = FALSE        
		∧ TrainPosition~[{TrainPosition(t)}] = {t}
	THEN 
		isTrainStationed(t) := TRUE		
	END
;
 repartir(t) =
	PRE 
		t ∈ isTrainStationed~[{TRUE}]
		∧ TrainPosition~[{TrainPosition(t)}] = {t}
	THEN 
		isTrainStationed(t) := FALSE
	END

END


