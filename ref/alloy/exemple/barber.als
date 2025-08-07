// Illustre le paradoxe identifié par Bertrand Russell
// ce qui força Cantor, l'auteur de la théorie des ensembles
// à raffiner sa théorie, car elle admettait des contradictions
// voir https://fr.wikipedia.org/wiki/Paradoxe_de_Russell
// https://fr.wikipedia.org/wiki/Paradoxe_du_barbier

// Dans ce paradoxe, on indique que le barbier
// rase tous les hommes qui ne se rasent pas eux-mêmes
// Il n'existe pas de modèle pour cette signature, ce qui 
// signifie qu'elle est incohérente
// si une telle spécification est ajoutée à une spécification
// alors on peut déduire ce que l'on veut dans cette théorie

sig Man {shaves: set Man}
one sig Barber extends Man {}
fact {
Barber.shaves = {m: Man | m not in m.shaves}
}
run {} for 3
