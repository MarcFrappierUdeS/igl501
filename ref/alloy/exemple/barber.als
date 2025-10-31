/* Illustre le paradoxe identifié par Bertrand Russell
ce qui força Cantor, l'auteur de la théorie des ensembles
à raffiner sa théorie, car elle admettait des contradictions
voir https://fr.wikipedia.org/wiki/Paradoxe_de_Russell
https://fr.wikipedia.org/wiki/Paradoxe_du_barbier

Dans ce paradoxe, on indique que le barbier
rase tous les hommes qui ne se rasent pas eux-mêmes

Le conseil municipal d'un village vote un arrêté municipal
qui enjoint à son barbier (masculin) de raser tous les habitants
masculins du village qui ne se rasent pas eux-mêmes et seulement ceux-ci.

Le barbier, qui est un habitant du village, n'a pas pu respecter cette règle car :

- S'il se rase lui-même, il enfreint la règle, car le barbier ne peut raser
   que les hommes qui ne se rasent pas eux-mêmes ;
- S'il ne se rase pas lui-même, il est en tort également,
   car il a la charge de raser les hommes qui ne se rasent pas eux-mêmes.

Il n'existe pas de modèle pour la  signature ci-dessous, qui représente
la règle imposée au barbier, ce qui 
signifie qu'elle est incohérente
si une telle spécification est ajoutée à une spécification
alors on peut déduire ce que l'on veut dans cette théorie, par la preuve
*/
sig Man {shaves: set Man}
one sig Barber extends Man {}
fact {
Barber.shaves = {m: Man | m not in m.shaves}
}
run {} for 3
