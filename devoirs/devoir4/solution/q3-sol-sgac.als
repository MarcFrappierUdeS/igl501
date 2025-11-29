module Consent
open util/relation

 sig Subject {
	subSucc : set Subject    
													 
}
fact
{
	acyclic[subSucc,Subject]
}

 sig Resource {
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

pred access[s:Subject, r:Resource]
{
let mins = minimals[applicable[s,r]] |
	some l : mins | l.mo = permission
		and no l' : mins | l'.mo = prohibition
}

fun applicable [s:Subject, r:Resource] : set Rule
{
	{ l : Rule | s in *subSucc.(l.su) and r in *resSucc.(l.re) }
}

fun accessible[]: Subject->Resource
{
   { s : Subject, r : Resource | access[s,r] }
}

// relation <<
pred precede[ l1,l2 : Rule]
{
	l1.pr < l2.pr
or
	(   l1.pr = l2.pr
  and	l1.su in ^subSucc.(l2.su)		
	)
}

fun minimals[AppRules : set Rule] : set Rule
{
	{ l : AppRules | no l': AppRules | precede[l',l] }
}

fun precedeRel[]: Rule -> Rule
{
{l1,l2:Rule | precede[l1,l2] }
}

fun precedence[]: Rule -> Rule
{
{l1,l2:Rule |
			l1 != l2
	and precede[l1,l2]
	and	no l':Rule-{l1+l2} |
				precede[l1,l'] and precede[l',l2]}
}

// données de test du devoir


one	sig S0, S1, S2, S3 extends Subject {}

one sig R0, R1, R2, R3 extends Resource {}

one sig L1, L2, L3, L4 extends Rule {}


run fig1 {
subSucc = S3 -> S1 + S3 -> S2 + S1 -> S0 + S2 -> S0

resSucc = R3 -> R1 + R3 -> R2 + R1 -> R0 + R2 -> R0

L1.pr = 1 and L1.su = S0 and L1.re = R0 and L1.mo = prohibition
L2.pr = 1 and L2.su = S1 and L2.re = R1 and L2.mo = prohibition
L3.pr = 1 and L3.su = S2 and L3.re = R1 and L3.mo = permission
L4.pr = 1 and L4.su = S3 and L4.re = R3 and L4.mo = permission
}

run test1 {
subSucc = S3 -> S1 + S3 -> S2 + S1 -> S0 + S2 -> S0

resSucc = R3 -> R1 + R3 -> R2 + R1 -> R0 + R2 -> R0

L1.pr = 2 and L1.su = S0 and L1.re = R0 and L1.mo = prohibition
L2.pr = 2 and L2.su = S1 and L2.re = R1 and L2.mo = prohibition
L3.pr = 2 and L3.su = S2 and L3.re = R1 and L3.mo = permission
L4.pr = 2 and L4.su = S0 and L4.re = R3 and L4.mo = permission
}


fun rule_show [r:Rule] : Subject -> Resource -> Int -> Modality
{
r.su -> r.re -> r.pr -> r.mo
}

check precedeRelAcyclic {
no (^precedeRel & iden)
	} for exactly 5 Subject, exactly 5 Resource, exactly 5 Rule

check precedeRelTransitive {
precedeRel.precedeRel in precedeRel
	} for exactly 5 Subject, exactly 5 Resource, exactly 5 Rule

check precedenRelIrreflexive {
no (iden & precedeRel)
	} for exactly 5 Subject, exactly 5 Resource, exactly 5 Rule

