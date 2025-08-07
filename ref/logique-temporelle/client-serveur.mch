MACHINE client_serveur

DEFINITIONS

/* chaque requête d'un client est éventuellement répondue
   faux, car on peut boucler sur le 2e serveur avant de traiter la réponse du serveur 1 */
  ASSERT_LTL0 == "G ([CaR(cl)] => F [RaC(cl)])" /* false */

/* chaque requête d'un client est éventuellement transmise à un serveur */
; ASSERT_LTL1 == "G ([CaR(cl)] => F ([RaS(cl,1)] or [RaS(cl,2)]))" /* true */

/* chaque requête d'un client est éventuellement répondable par un serveur */
; ASSERT_LTL2 == "G ([CaR(cl)] => F (e(SaR(cl,1)) or e(SaR(cl,2))))" /* true */

/* chaque requête d'un client est éventuellement répondue sur un chemin */
; ASSERT_CTL1 == "AG ([CaR(cl)] => EF [RaC(cl)])" /* true */

/* chaque requête d'un client est transmise à un serveur */
; ASSERT_CTL2 == "[CaR(1)] => EF {etatRequete={}}" /* true */

/* il est toujours possible de revenir à un état où les requêtes sont tranmises aux serveur */
; ASSERT_CTL3 == "AG EF {etatRequete={}}" /* true */

/* il est toujours possible de revenir à l'état initial du système */
; ASSERT_CTL4 == "AG EF {client = CLIENT * {C0} &  serveur = SERVEUR * {S0} &  etatRequete = {} &  etatReponse = {} & serveurRequete = {}}" /* true */
				
; ASSERT_CTL5 == "EG {etatRequete={}}" /* false */
	
; ASSERT_CTL6 == "AF {etatRequete={}}" /* true */

; ASSERT_CTL7 == "E({etatRequete/={}} U {etatRequete={}})" /* parsing error */
		
SETS	
  EtatClient = {C0, C1};	
  EtatServeur = {S0,S1};
  EtatRequete = {RQ0, RQ1};
  EtatReponse = {RP0, RP1}

CONSTANTS CLIENT, SERVEUR, nbClient, nbServeur, cl, sv

PROPERTIES
  nbClient = 2
& nbServeur = 2
& CLIENT = 1..nbClient
& SERVEUR = 1..nbServeur
& cl : CLIENT
& sv : SERVEUR

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

