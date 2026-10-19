MACHINE Train

SETS
    TRAIN

CONSTANTS max_segment, SEGMENT

PROPERTIES
    max_segment : 1..MAXINT
&   SEGMENT = 1..max_segment

VARIABLES
    train, position, stationnement

INVARIANT
    train <: TRAIN
&   position : train >+> SEGMENT
&   stationnement : train >+> SEGMENT
&   train = dom(position) \/ dom(stationnement)
&   dom(position) /\ dom(stationnement) = {}

INITIALISATION
    train := {}
||  position := {}
||  stationnement := {}

OPERATIONS

    ajouter_train(tt,ss) = 
    PRE
        tt : TRAIN
    &   tt /: train
    &   ss : SEGMENT
    &   ss /: ran(position)
    THEN
        train := train \/ {tt}
    ||  position(tt) := ss
    END
;
    avancer(tt) =
    PRE
        tt : TRAIN
    &   tt : train
    &   tt : dom(position)
    &   position(tt)+1 /: ran(position)
    &   position(tt) /= max_segment
    THEN
        position(tt) := position(tt)+1
    END
;
    stationner(tt) =
    PRE
        tt : TRAIN
    &   tt : train
    &   tt : dom(position)
    &   position(tt) /: ran(stationnement)
    THEN
        position := {tt}<<|position
    ||  stationnement(tt) := position(tt)
    END
;
    repartir(tt) =
    PRE
        tt : TRAIN
    &   tt : train
    &   tt : dom(stationnement)
    &   stationnement(tt) /: ran(position)
    THEN
        stationnement := {tt}<<|stationnement
    ||  position(tt) := stationnement(tt)
    END
END

