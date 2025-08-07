abstract sig Personne
{
pere : lone Homme,
mere : lone Femme,
parent : set Personne
}

sig Homme, Femme extends Personne {}

// Fondateur est un sous-ensemble de Personne
sig Fondateur in Personne {}

fact {
parent = pere + mere
// pas de cycle dans les parents
all p : Personne | not (p in p.^parent)
// pas d'inceste, c'est-à-dire par de parent qui est aussi un ancêtre
// (grand-parent, ou arrière-grand-parent, ...)
no p,p' : Personne | p' in (p.parent & p.(parent.^parent))
// pas d'enfant entre frere et soeur ou cousin
no p1,p2,p3 : Personne |
	p3.parent = p1+p2 and (p1 in p2.fraterie or p1 in p2.cousins)
// toute personne sauf les fondateurs ont un parent
all p : Personne-Fondateur | some p.pere and some p.mere
// les fondateurs n'ont pas de parent
all p : Fondateur | no p.parent
}

fun grand_parents[]:Personne->Personne
{
parent.parent
}

fun fraterie[]: Personne->Personne
{
(parent.~parent)-iden
}

fun cousins_de[p:Personne]: set Personne
{
p.grand_parents.(~grand_parents)-fraterie[p]-p
}

fun cousins: Personne->Personne
{
grand_parents.(~grand_parents)-fraterie-iden
}

pred cousin[x,y:Personne]
{
x in y.cousins
}

run test1 {some x,y : Personne | x in grand_parents[y]} for  7 Personne
run test2 {some Personne and Fondateur in Personne.grand_parents} for  7 Personne
run test3 {some x,y : Personne |cousin[x,y]} for  12 Personne
run test4 {some x,y : Personne |x in fraterie[y]} for  8 Personne

check verifier_consanguin {
all p1,p2,p3 : Personne |
	p2 in p1.parent and p3 in p1.parent
  =>
  not (p2 in fraterie[p3] or p2 in cousins[p3])
} for  8 Personne

/* Un exemple particulier de parent */
/*
one sig H1,H2,H3,H4 extends Homme {}
one sig F1,F2,F3 extends Femme {}

fact {
pere = H3->H1 + F3->H2 + H4->H3
mere = H3->F1 + F3->F2 + H4->F3
}
*/
