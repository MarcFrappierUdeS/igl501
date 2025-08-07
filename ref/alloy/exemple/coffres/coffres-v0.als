open util/ordering[State] 
enum Event {init,insererCle, enleverCle, ouvrirPorte, fermerPorte}
sig Coffre {}
abstract sig Cle {}
one sig CleBanque extends Cle {}
sig CleClient extends Cle {
  coffre : one Coffre // indique le coffre associé à une clé
}

fact {coffre in CleClient one -> one Coffre} // bijection coffre

abstract sig EtatVerrou {}
one sig Verrouille, Deverouille extends EtatVerrou {}
abstract sig EtatPorte {}
one sig Ouverte, Fermee extends EtatPorte {}
sig State {
  verrou : Coffre -> one EtatVerrou,
  clesIns : Coffre -> set Cle,  // les clés insérées dans un coffre
  porte : Coffre -> one EtatPorte,
  event : Event
}

pred insererCle[s,s' : State, c : Coffre, k : Cle]
{
  not (k in Coffre.(s.clesIns))
  #c.(s.clesIns) < 2
  getclesIns[s',c]  =  getclesIns[s,c] + k
  noChangeclesInsBut[s,s',c]
  getclesIns[s',c] = CleBanque + cleDuCoffre[c] =>
    (getEtatVerrou[s',c] = Deverouille)
  not (getclesIns[s',c] = CleBanque + cleDuCoffre[c]) =>
    (getEtatVerrou[s',c] = Verrouille)
  noChangeVerrouBut[s,s',c]
  noChangePorte[s,s']
  s'.event = insererCle
}

pred enleverCle[s,s' : State, c : Coffre, k : Cle]
{
  k in getclesIns[s,c]
  getclesIns[s',c]  =  getclesIns[s,c] - k
  getEtatVerrou[s',c] = Verrouille
  noChangeclesInsBut[s,s',c]
  noChangeVerrouBut[s,s',c]
  noChangePorte[s,s']
  s'.event = enleverCle
}

pred ouvrirPorte[s,s' : State, c : Coffre]
{
  getEtatPorte[s,c] = Fermee
  getEtatVerrou[s,c] = Deverouille
  getEtatPorte[s',c] = Ouverte
  noChangeclesIns[s,s']
  noChangeVerrou[s,s']
  noChangePorteBut[s,s',c]
  s'.event = ouvrirPorte
}

pred fermerPorte[s,s' : State, c : Coffre]
{
getEtatPorte[s,c] = Ouverte
getEtatPorte[s',c] = Fermee
noChangeclesIns[s,s']
noChangeVerrou[s,s']
noChangePorteBut[s,s',c]
s'.event = fermerPorte
}

pred noChangeclesIns[s,s' : State] {s'.clesIns = s.clesIns}
pred noChangeclesInsBut[s,s' : State, c : Coffre] {
  all c' : Coffre-c | getclesIns[s',c'] = getclesIns[s,c']
}
pred noChangeVerrou[s,s' : State] {s'.verrou = s.verrou}
pred noChangeVerrouBut[s,s' : State, c : Coffre] {
  all c' : Coffre-c | getEtatVerrou[s',c'] = getEtatVerrou[s,c']
}
pred noChangePorte[s,s' : State] {s'.porte = s.porte}
pred noChangePorteBut[s,s' : State, c : Coffre] {
  all c' : Coffre-c | getEtatPorte[s',c'] = getEtatPorte[s,c']
}
fun getEtatVerrou[s : State, c : Coffre]:EtatVerrou { c.(s.verrou) }
fun getEtatPorte[s : State, c : Coffre]:EtatPorte { c.(s.porte) }
fun getclesIns[s : State, c : Coffre]:set Cle { c.(s.clesIns) }
fun cleDuCoffre[c : Coffre]:Cle { coffre.c }

pred Init[s:State]
{
  Coffre.(s.porte ) = Fermee
  Coffre.(s.verrou  ) = Verrouille
  no Coffre.(s.clesIns )
  s.event = init
}

pred TraceValide[]
{
		Init[first]
and	all s : State-last |	let s' = next[s]	| Transition[s,s']
}

pred Transition[s,s':State]
{
  some c : Coffre, k : Cle |
    insererCle[s,s',c,k] or
    enleverCle[s,s',c,k] or
    ouvrirPorte[s,s',c] or
    fermerPorte[s,s',c]
}

fact {TraceValide[]}

/* Vérifier que le système peut exécuter au moins une trace */
run coherence {TraceValide[]} for 2 but exactly 3 Cle, exactly 2 Coffre, 5 State

pred invVerrou[s : State]
{
  all c : Coffre |
    getEtatVerrou[s,c]=Deverouille
    <=>
    getclesIns[s,c] = CleBanque + cleDuCoffre[c]
}

check invVerrouInit {
all s : State | Init[s] => invVerrou[s]
} for 2 but 3 Cle, 1 State

check invVerrouTrans {
all s,s' : State | invVerrou[s] and Transition[s,s'] => invVerrou[s']
} for 2 but 3 Cle, 10 State

run ouvrirPorte {
   some s1 : State-last | let s2 = next[s1]	| let s3 = next[s2] |  let s4 = next[s3]	| 
    some c : Coffre |
      insererCle[s1,s2,c,cleDuCoffre[c]] and
      insererCle[s2,s3,c,CleBanque] and
      ouvrirPorte[s3,s4,c]
}  for 2 but 3 Cle, 4 State


check ouvrirApresInsertion {
		all s : State-last | 	let s' = next[s]	| 
		all c : Coffre |
		ouvrirPorte[s,s',c] =>
        some s1,s2,s3,s4 : State-nexts[s] |
              (
			        insererCle[s1,s2,c,cleDuCoffre[c]] and
    			    insererCle[s3,s4,c,CleBanque]
              )
}  for 2 but 3 Cle, 10 State
