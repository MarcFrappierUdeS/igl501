module Consent
open util/relation

abstract sig Subject {
	subSucc : set Subject    												 
}

fact
{
	acyclic[subSucc,Subject]
}

abstract sig Resource {
	resSucc : set Resource    
}

fact
{
	acyclic[resSucc,Resource]
}

abstract sig Modality {}
one sig permission extends Modality {}
one sig prohibition extends Modality {}
abstract sig Rule {
	pr : one Int,          // priority of the rule
	su : one Subject,
	re : one Resource,
	mo : one Modality
}{
  pr >= 0
}

// retourne vrai ssi s a accès à r
pred access[s:Subject, r:Resource]
{
// à compléter
}

// retourne les règles applicables à une requête (s,r)
fun applicable [s:Subject, r:Resource] : set Rule
{
// à compléter
}

// retourne les couples (s,r) tels que s a accès à r
fun accessible[]: Subject->Resource
{
// à compléter
}

// retoune vrai ssi l1 << l2
pred precede[ l1,l2 : Rule]
{
// à compléter
}

fun minimals[AppRules : set Rule] : set Rule
{
// à compléter
}

// retourne le graphe de précédence de la relation <<
fun precedence[]: Rule -> Rule
{
// à compléter
}

// déclaration des sujets, des ressources et des règles
one	sig S0, S1, S2, S3 extends Subject {}

one sig R0, R1, R2, R3 extends Resource {}

one sig L1, L2, L3, L4 extends Rule {}

// test de l'exmple de la figure 1
run fig1 {
subSucc = S3 -> S1 + S3 -> S2 + S1 -> S0 + S2 -> S0

resSucc = R3 -> R1 + R3 -> R2 + R1 -> R0 + R2 -> R0

L1.pr = 1 and L1.su = S0 and L1.re = R0 and L1.mo = prohibition
L2.pr = 1 and L2.su = S1 and L2.re = R1 and L2.mo = prohibition
L3.pr = 1 and L3.su = S2 and L3.re = R1 and L3.mo = permission
L4.pr = 1 and L4.su = S3 and L4.re = R3 and L4.mo = permission
}

// autre exemple de test
run test1 {
subSucc = S3 -> S1 + S3 -> S2 + S1 -> S0 + S2 -> S0

resSucc = R3 -> R1 + R3 -> R2 + R1 -> R0 + R2 -> R0

L1.pr = 2 and L1.su = S0 and L1.re = R0 and L1.mo = prohibition
L2.pr = 2 and L2.su = S1 and L2.re = R1 and L2.mo = prohibition
L3.pr = 2 and L3.su = S2 and L3.re = R1 and L3.mo = permission
L4.pr = 2 and L4.su = S0 and L4.re = R3 and L4.mo = permission
}

// fonction utilitaire qui affiche une règle sous la forme d'un tuple
fun rule_show [r:Rule] : Subject -> Resource -> Int -> Modality
{
r.su -> r.re -> r.pr -> r.mo
}
