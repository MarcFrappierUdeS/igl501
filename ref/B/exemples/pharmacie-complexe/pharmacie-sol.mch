MACHINE pharmacie

SETS

  PATIENT = {p1,p2,p3}
; MEDICAMENT = {m1,m2,m3}
; SEXE = {masculin,feminin} // Sexe biologique
; DESCRIPTION = {d1,d2,d3}

DEFINITIONS
  symmetrique(r) == (r ∪ r⁻¹)

VARIABLES

    /* entités */
    patient, medicament, 

    /* attributs */
    idPatient, idRAMQ, age,
    idMedic, DIN, description, ageMin,

    /* associations */
    incompatibilite, allergie, prescription, sexe, restriction

INVARIANT

/* Entités */

    patient ⊆ PATIENT
  ∧ medicament ⊆ MEDICAMENT

/* Attributs des entités */

  ∧ idPatient ∈ patient >-> NAT
  ∧ idRAMQ ∈ patient >-> NAT
  ∧ age ∈ patient ⇸ NAT
  ∧ idMedic ∈ medicament >-> NAT
  ∧ DIN ∈ medicament >+> NAT
  ∧ description ∈ medicament >-> DESCRIPTION
  ∧ ageMin ∈ medicament ⇸ NAT

/* Associations entre les entités */

  ∧ allergie ∈ patient ↔ medicament
  ∧ incompatibilite ∈ medicament ↔ medicament
  ∧ prescription ∈ patient ↔ medicament
  ∧ sexe ∈ patient ↔ SEXE
  ∧ restriction ∈ medicament ⇸ SEXE

/* Contraintes sur les associations */

/* Un médicament n'est pas incompatible avec lui-même */

  ∧ id(medicament) ∩ incompatibilite = ∅

/* One ne prescrit pas à un PATIENT deux médicaments qui sont incompatibles */

  ∧ (prescription⁻¹ ; prescription) ∩ incompatibilite = ∅

/* On ne prescrit pas à un PATIENT un médicament auquel il est allergique */

  ∧ allergie ∩ prescription = ∅

/* Un medicament restreint à un sexe ne peut être prescrit qu'à des patients qui ont seulement ce sexe */

  ∧ 
      ∀(p,m,s).
        (
             (p,m) ∈ prescription
           ∧ (m,s) ∈ restriction
        ⇒
            sexe[{p}] = {s}
        )

/* Si un medicament a un age minimal pour être prescrit, alors le patient doit avoir cet age minimal */

  ∧ ∀(p,m,n).
      (
            (p,m) ∈ prescription
          ∧ (m,n) ∈ ageMin
      ⇒
          ∃k.( (p,k) ∈ age ∧ k ≥ n )
      )

INITIALISATION

//patient, medicament, idPatient, idRAMQ, age, idMedic, DIN, description, ageMin, incompatibilite, allergie, prescription, sexe, restriction := ∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅

      patient := PATIENT
  ||  medicament := MEDICAMENT
  ||  idPatient := {(p1,1),(p2,2),(p3,3)}
  ||  idRAMQ := {(p1,1),(p2,2),(p3,3)}
  ||  age := {(p1,1),(p2,2)}
  ||  idMedic := {(m1,1),(m2,2),(m3,3)}
  ||  DIN := {(m1,1),(m2,2),(m3,3)}
  ||  description := {(m1,d1),(m2,d2),(m3,d3)}
  ||  ageMin := {(m2,2)}
  ||  allergie := {(p3,m1),(p2,m2),(p3,m3)}
  ||  incompatibilite := {(m2,m3)}
  ||  prescription := ∅
  ||  sexe := {(p1,masculin),(p2,feminin),(p3,masculin),(p3,feminin)}
  ||  restriction := {(m3,masculin)}

OPERATIONS

prescrire(p,m) =
PRE
    p ∈ patient
  ∧ m ∈ medicament
  ∧ (p,m) ∉ allergie
  ∧ ¬ (∃m1.(m1 ∈ medicament ∧ (p,m1) ∈ prescription ∧ (m,m1) ∉ symmetrique(incompatibilite)))
  ∧ (m ∈ dom(restriction) ⇒ restriction(m) ∈ sexe[{p}])
  ∧ (m ∈ dom(ageMin) ⇒ p ∈ dom(age) ∧ age(p) ≥ ageMin(m))
THEN
  prescription := prescription ∪ {(p,m)}

END
END
