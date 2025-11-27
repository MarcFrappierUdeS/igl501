MACHINE q3

SETS
  EtatClient = {C0, C1};
  EtatServeur = {S0, S1};
  EtatRequete = {RQ0, RQ1};
  EtatReponse = {RP0, RP1}

CONSTANTS CLIENT, SERVEUR, nbClient, nbServeur

PROPERTIES
    nbClient = 2
  & nbServeur = 2
  & CLIENT = 1..nbClient
  & SERVEUR = 1..nbServeur

VARIABLES client, serveur, etatRequete, etatReponse, serveurRequete

INVARIANT
    client : CLIENT --> EtatClient
  & serveur : SERVEUR --> EtatServeur
  & etatRequete <: CLIENT
  & card(etatRequete) <= 1
  & etatReponse <: CLIENT
  & card(etatReponse) <= 1
  & serveurRequete : CLIENT +-> SERVEUR


INITIALISATION
      client := CLIENT * {C0}
  ||  serveur := SERVEUR * {S0}
  ||  etatRequete := {}
  ||  etatReponse := {}
  ||  serveurRequete := {}

OPERATIONS

CaR(c) =
  PRE
      c : CLIENT
    & client(c) = C0
    & etatRequete = {}
  THEN
       etatRequete := {c}
    || client(c) := C1
  END
;
RaS(c,s) =
  PRE
      c : CLIENT
    & s : SERVEUR
    & client(c) = C1
    & serveur(s) = S0
    & etatRequete = {c}
  THEN
        serveur(s) := S1
    ||  etatRequete := {}
    ||  serveurRequete(c) := s
  END
;
SaR(c,s) =
  PRE
      c : CLIENT
    & s : SERVEUR
    & serveur(s) = S1
    & etatReponse = {}
    & c |-> s : serveurRequete
    THEN
        serveur(s) := S0
    ||  etatReponse := {c}
    ||  serveurRequete := {c} <<| serveurRequete
  END
;
RaC(c) =
  PRE
      c : CLIENT
    & client(c) = C1
    & etatReponse = {c}
  THEN
        client(c) := C0
    ||  etatReponse := {}
  END

END

