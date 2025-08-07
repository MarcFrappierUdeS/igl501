MACHINE Q4
SETS
  COURTIER = {c1,c2};
  SUPERVISEUR = {s1,s2};
  TRANSACTION = {t1,t2,t3,t4,t5}
DEFINITIONS
  somme(S) == SIGMA(z).(z : S | z)
VARIABLES
  courtier, superviseur, supervisePar, limiteQuotidienne, limiteParTransaction, limiteGlobale, transaction, montant, auteur, transactionEnAttente, approbation, refus

INVARIANT
    courtier <: COURTIER
  & superviseur <: SUPERVISEUR
  & supervisePar : courtier --> superviseur
  & limiteQuotidienne : courtier --> NAT
  & limiteGlobale : NAT
  & limiteParTransaction : courtier --> NAT
  & transaction <: TRANSACTION
  & montant : transaction --> NAT
  & auteur : transaction --> courtier
  & transactionEnAttente <: transaction
  & approbation : transaction +-> superviseur
  & refus : transaction +-> superviseur

  /* La somme des transactions ne depasse pas la limite du courtier */
  & !(c).(c : courtier => somme(montant[auteur~[{c}]-dom(refus)]) <= limiteQuotidienne(c))

  /* La limite quotidienne d'un courtier ne dépasse pas la limite de la firme */
  & !(c).(c : courtier => limiteQuotidienne(c) <= limiteGlobale)

  /* Les transactions en attente ont besoin d'etre approuvees */
  & !(t). ( t : transactionEnAttente
          =>
            montant(t) > limiteParTransaction(auteur(t))
          )

  /* Les transaction completees sont approuvees si necessaire */
  & !(t). (   t : transaction
            & t /: transactionEnAttente
            & montant(t) > limiteParTransaction(auteur(t))
          =>
            t |-> supervisePar(auteur(t)) : (approbation \/ refus)
          )
  /* Une transaction est soit en attente, soit approuvee ou refusee */
  & (dom(approbation) \/ dom(refus)) /\ transactionEnAttente = {}
  & dom(approbation) /\ dom(refus) = {}

INITIALISATION
      courtier :=  COURTIER
  ||  superviseur := SUPERVISEUR
  ||  supervisePar := {c1 |-> s1, c2 |-> s2}
  ||  limiteQuotidienne := {c1 |-> 2, c2 |-> 3}
  ||  limiteGlobale := 3
  ||  limiteParTransaction := {c1 |-> 1, c2 |-> 2}
  ||  transaction := {}
  ||  montant := {}
  ||  auteur := {}
  ||  transactionEnAttente := {}
  ||  approbation := {}
  ||  refus := {}


OPERATIONS
  transiger(c,m) =
  PRE
      c : courtier
    & m : NAT1
    & somme(montant[auteur~[{c}]-dom(refus)]) + m <= limiteQuotidienne(c)
    & TRANSACTION - transaction /= {}
  THEN
    ANY t
    WHERE
      t : TRANSACTION - transaction
    THEN
          transaction := transaction \/ {t}
      ||  IF
            m > limiteParTransaction(c)
          THEN
            transactionEnAttente := transactionEnAttente \/ {t}
          END
      ||  auteur(t) := c
      ||  montant(t) := m
    END
  END;

  approuver(s,t) =
  PRE
      s : superviseur
    & s = supervisePar(auteur(t))
    & t : transactionEnAttente
/*    & t /: (dom(approbation) ∪ dom(refus))
    & montant(t) > limiteParTransaction(auteur(t)) */
  THEN
        transactionEnAttente := transactionEnAttente - {t}
    ||  approbation(t) := s
  END;

  refuser(s,t) =
  PRE
      s : superviseur
    & s = supervisePar(auteur(t))
    & t : transactionEnAttente
/*    & t /: (dom(approbation) \/ dom(refus))
    & montant(t) > limiteParTransaction(auteur(t)) */
  THEN
        transactionEnAttente := transactionEnAttente - {t}
    ||  refus(t) := s
  END
END
