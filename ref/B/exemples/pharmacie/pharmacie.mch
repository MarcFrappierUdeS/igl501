MACHINE pharmacie

SETS
    PATIENT = {p1,p2};
    MEDICAMENT = {m1,m2}

DEFINITIONS

    noyau(rr) == ((rr)~ ; rr);
    fermeture_symmetrique(rr) == (rr \/ rr~)

VARIABLES
    patient, medicament, incompatibilite, allergie, prescription

INVARIANT
    patient <: PATIENT
  & medicament <: MEDICAMENT
  & allergie : patient <-> medicament
  & incompatibilite : medicament <-> medicament
  & prescription : patient <-> medicament
  & id(MEDICAMENT) /\ incompatibilite = {}
  & noyau(prescription) /\ incompatibilite = {}
  & allergie /\ prescription = {}

INITIALISATION
      patient := {}
  ||  medicament := {}
  ||  incompatibilite := {}
  ||  allergie := {}
  ||  prescription := {}

OPERATIONS

creerPatient(pp) =

    PRE
        pp : PATIENT - patient
    THEN
        patient := patient \/ {pp}
    END;

creerMedicament(mm) =

    PRE
        mm : MEDICAMENT - medicament
    THEN
        medicament := medicament \/ {mm}
    END;

supprimerMedicament(mm) =

    PRE
        mm : medicament &
        mm /: (ran(allergie) \/ dom(incompatibilite) \/ ran(incompatibilite) \/ ran(prescription))
    THEN
        medicament := medicament - {mm}
    END;

incompatibles(mm1,mm2) =

    PRE
        mm1 : medicament
      & mm2 : medicament
      & mm1 /= mm2
      & mm1 |-> mm2 /: fermeture_symmetrique(incompatibilite)
      & mm1 |-> mm2 /: noyau(prescription)
      & mm2 |-> mm1 /: noyau(prescription)
    THEN
        incompatibilite := incompatibilite \/ {mm1 |-> mm2}
    END;

allergique(pp,mm) =

    PRE
        pp : patient
      & mm : medicament
      & pp |-> mm /: prescription
      & pp |-> mm /: allergie
    THEN
        allergie := allergie \/ {pp |-> mm}
    END;

prescrire(pp,mm) =

    PRE
        pp : patient
      & mm : medicament
      & pp |-> mm /: allergie
      & pp |-> mm /: prescription
      & noyau(prescription \/ {pp|->mm}) /\ incompatibilite = {}
    THEN
        prescription := prescription \/ {pp |-> mm}
    END
END
