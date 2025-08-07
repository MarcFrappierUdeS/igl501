-- Système de gestion des accès dans un batiment

open util/ordering[Etat]

enum Evenement {init, autoriser, revoquer, deplacer}

sig Batiment {
estDans : lone Batiment}

sig Piece extends Batiment {
porte : set Piece
}

fact {
porte = ~porte
no (porte & iden)
}

one sig Exterieur extends Piece {}

fact {
-- pas de cycle dans estDans
no iden & ^estDans
-- pas de batiment sans piece
all b:Batiment-Piece | some estDans.b
-- chaque piece, sauf extérieur, est dans un batiment
(Piece-Exterieur) in estDans.Batiment
-- Extérieur est dans aucun batiment
Exterieur not in estDans.Batiment
-- Aucun batiment dans une pièce
no estDans.Piece
-- chaque piece est accessible de l'extérieur
Exterieur->(Piece-Exterieur) in ^porte
-- Un seul bâtiment racine
#(Batiment-estDans.Batiment)=2
}

sig Personne {}

sig Etat { 
autorisation : Personne -> Batiment,
position : Personne -> Piece,
event : Evenement
}

/*-------------------------
    INITIALISATION
--------------------------*/
pred Init [E:Etat]
{
	E.autorisation = Personne -> Exterieur -- aucune autorisation, sauf être à l'extérieur
	E.position = Personne -> Exterieur -- toute personne est à l'extérieur du batiment
	E.event = init
}

/*-------------------
      Autoriser
  -------------------*/
pred Autoriser[p:Personne, b:Batiment,E,E':Etat]
{
-- précondition
b != Exterieur
not (p->b in E.autorisation) -- pas dejà autorisé
-- maj etat
E'.autorisation = E.autorisation + p->b
-- nochange
E'.position = E.position
E'.event=autoriser
}

/*-------------------
      Revoquer
  -------------------*/
pred Revoquer[p:Personne, b:Batiment,E,E':Etat]
{
-- précondition
b != Exterieur
-- autorisé à ce batiment
p->b in E.autorisation 
-- ne doit pas revoquer de sortir du batiment
let pi_aut = p.(E.autorisation-p->b).*~estDans |
    Exterieur in (p.(E.position)).*(porte & pi_aut->pi_aut)
-- maj etat
E'.autorisation = E.autorisation - p->b
-- nochange
E'.position = E.position
E'.event=revoquer
}

/*-------------------
      Deplacer
  -------------------*/
pred Deplacer[pe:Personne, pi:Piece,E,E':Etat]
{
-- précondition
pi != pe.(E.position)
pe->pi in (E.autorisation).*~estDans -- autoriser à cette pièce
pe.(E.position)->pi in porte         -- porte vers cette pièce à partir de la pièce actuelle
-- maj etat
E'.position = E.position ++ pe->pi
-- nochange
E'.autorisation = E.autorisation
E'.event=deplacer
}

pred Inv[E:Etat]
{
-- chaque personne est dans une pièce
E.position.Piece = Personne
-- position est une fonction
E.position in Personne -> lone Piece
-- une personne est dans une piece autorisée
E.position in (E.autorisation).*~estDans
}

pred Transition[E,E':Etat]
{
some pe:Personne, pi:Piece, b:Batiment |
			Autoriser[pe,b,E,E']
	or  Revoquer[pe,b,E,E']
	or 	Deplacer[pe,pi,E,E']
}

check Invariant_Init
{
	all E : Etat | Init[E] => Inv[E]
} for 1 Etat, 2 Personne, 3 Batiment

check Invariant_Transition
{
	all E,E':Etat | Inv[E] and Transition[E,E'] =>Inv[E']
} for 2 Etat, 2 Personne, 5 Batiment

pred TraceValide[]
{
		Init[first]
and	all s : Etat-last |	let s' = next[s]	| Transition[s,s']
}

run showTrace1
{
TraceValide[]
#(event.deplacer)=2
some p : Piece-Exterieur | Exterieur->p not in porte
//Personne.(last.position)=P2
} for 5 Etat,  exactly 2 Personne, 5 Batiment

run showTrace2
{
TraceValide[]
#(event.revoquer)=1
} for 5 Etat,  exactly 2 Personne, 5 Batiment

run showWorld {} for 1 Etat, exactly 2 Personne, 6 Batiment

fun restrict[r : univ -> univ, s:set univ] : univ->univ
{
r & (s -> s)
}

one sig P1,P2 extends Piece {}
one sig B1,B2 extends Batiment {}
fact {
estDans = P1 -> B1 + P2->B1 + B1->B2
porte = Exterieur -> P1 + P1 -> Exterieur +
        P1 -> P2 + P2->P1
}


