MACHINE q4

SETS
 PERSONNE={p1,p2}; TACHE={t1,t2}; COMPETENCE={c1,c2}; RESSOURCE={r1,r2}

CONSTANTS k

PROPERTIES
  k = 1

DEFINITIONS
  SET_PREF_MININT == 0;
  SET_PREF_MAXINT == 1

VARIABLES
  personne, tache, ressource, competence, affectee, dispose,
  necessite, utiliseePar, requiert, dateDebut, dateFin

INVARIANT
    personne <: PERSONNE                                   /* entite */
  & tache <: TACHE                                         /* entite */
  & ressource <: RESSOURCE                                 /* entite */
  & competence <: COMPETENCE                               /* entite */
  & dispose : personne <-> competence                      /* relation (d) */
  & necessite : tache <-> competence                       /* relation (d) */
  & requiert : tache <-> ressource                         /* relation (f) */
  & affectee : personne <-> tache                          /* relation */
  & utiliseePar : ressource +-> tache /* relation */       /* relation, (g) => fonction */
  & dom(dispose) = personne                                /* cardinalite min 1 */
  & dom(necessite) = tache                                 /* cardinalite min 1 */
  & !(p).(p:personne => card( {p} <| affectee ) <= k)      /* (c), cardinalite max 4 */
  & !(p,t).(   p:personne & t:tache & (p,t) : affectee
            => necessite[{t}] <: dispose[{p}])             /* (e) */
  & !(r).(r:ressource => utiliseePar(r) : requiert~[{r}])  /* (j) */
  & dateDebut : tache +-> NAT                              /* (a) */
  & dateFin : tache +-> NAT                                /* (a) */
  & dom(dateFin) <: dom(dateDebut)                         /* (b) */
  & !(t).(t : dom(dateFin) => dateDebut(t) < dateFin(t))   /* (b) */
  &    (ran(affectee) \/ ran(utiliseePar))
    <: (dom(dateDebut)-dom(dateFin))                       /* (h),(i) */

INITIALISATION
  personne, tache, ressource, competence, affectee, dispose, necessite, utiliseePar, requiert, dateDebut, dateFin
  :=
  {p1,p2},{t1,t2},{r1,r2},{c1,c2},{},{(p1,c1),(p1,c2),(p2,c2)},{(t1,c1),(t2,c2)},{},{(t1,r1),(t1,r2)},{(t1,0),(t2,0)},{}

OPERATIONS

  AffecterPersonne(p,t) =
  PRE
      p : personne
    & t : tache
    & (p,t) /: affectee
    & necessite[{t}] <: dispose[{p}]
    & card( {p} <| affectee ) < k
    & t : dom(dateDebut)
    & t /: dom(dateFin)
  THEN
    affectee := affectee \/ {(p,t)}
  END;

  AffecterRessource(r,t) =
  PRE
      r : ressource
    & t : tache
    & r : requiert[{t}]
    & t : dom(dateDebut)
    & t /: dom(dateFin)
    & r /: dom(utiliseePar)
  THEN
    utiliseePar(r) := t
  END;

  TerminerTache(t,d) =
  PRE
      t : tache
    & t : dom(dateDebut)
    & t /: dom(dateFin)
    & d : NAT
    & d > dateDebut(t)
  THEN
        dateFin(t) := d
    ||  affectee := affectee |>> {t}
    ||  utiliseePar := utiliseePar |>> {t}
  END

END









