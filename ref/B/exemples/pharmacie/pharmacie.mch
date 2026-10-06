MACHINE

    pharmacie

DEFINITIONS

    noyau(rr) == ((rr)~ ; rr)

VARIABLES
    patient, nom, medicament, description,
    incompatibilite, allergie, prescription

INVARIANT
    patient <: NAT &
    nom : patient -->  STRING &
    medicament <: NAT &
    description : medicament --> STRING &
    allergie : patient <-> medicament &
    incompatibilite : medicament <-> medicament &
    prescription : patient <-> medicament &
    noyau(prescription) /\ incompatibilite = {} &
    allergie /\ prescription = {}

INITIALISATION
    patient := {} ||
    nom := {} ||
    medicament := {} ||
    description := {} ||
    incompatibilite := {} ||
    allergie := {} ||
    prescription := {}

OPERATIONS

creerPatient(pp, nm) =

    PRE
        pp : NAT - patient &
        nm : STRING
    THEN
        patient := patient \/ {pp} ||
        nom(pp) := nm
    END;

creerMedicament(mm, dd) =

    PRE
        mm : NAT - medicament &
        dd : STRING
    THEN
        medicament := medicament \/ {mm} ||
        description(mm) := dd
    END;

supprimerMedicament(mm) =

    PRE
        mm : medicament &
        mm /: (ran(allergie) \/ dom(incompatibilite) \/ ran(incompatibilite) \/ ran(prescription))
    THEN
        medicament := medicament - {mm} ||
        description := {mm} <<| description
    END;

incompatibles(mm1,mm2) =

    PRE
        mm1 : medicament &
        mm2 : medicament &
        mm1 |-> mm2 /: noyau(prescription) &
        mm2 |-> mm1 /: noyau(prescription)
    THEN
        incompatibilite := incompatibilite \/ {mm1 |-> mm2}
    END;

allergique(pp,mm) =

    PRE
        pp : patient &
        mm : medicament &
        pp |-> mm /: prescription
    THEN
        allergie := allergie \/ {pp |-> mm}
    END;

prescrire(pp,mm) =

    PRE
        pp : patient &
        mm : medicament &
        pp |-> mm /: allergie &
        noyau(prescription \/ {pp|->mm}) /\ incompatibilite = {}
	
    THEN
        prescription := prescription \/ {pp |-> mm}
    END
END
