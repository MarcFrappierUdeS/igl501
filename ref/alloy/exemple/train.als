open util/ordering[State] 
enum Event {init,ajouter, avancer, garer, repartir}
sig Train {}
sig State {
trains : set Train,
position : Train -> Int,
stationnement : Train -> Int,
event : Event
}

pred Inv[s:State]
{
s.position in Train lone -> lone Int
s.stationnement in Train lone -> lone Int
s.trains = s.position.Int  + s.stationnement.Int
no (s.position.Int  & s.stationnement.Int)
}

check InvEquivInv2 {
all s : State | Inv[s] <=> Inv2[s]
}

pred Inv2[s:State]
{
//s.position in Train lone -> lone Int
all t1:s.position.Int | one t1.(s.position) // position est une fonction
all t1,t2:s.position.Int | t1.(s.position)=t2.(s.position) => t1=t2 // injective
s.stationnement in Train lone -> lone Int
s.trains = s.position.Int  + s.stationnement.Int
no (s.position.Int  & s.stationnement.Int)
}

pred Init[s:State]
{
no s.trains
no s.position
no s.stationnement
s.event = init
}

pred Ajouter[t:Train, p:Int, s,s':State ]
{
p > 0
t not in s.trains
//p not in Train.(s.position)
s'.trains = s.trains + t
s'.position = s.position + t->p
s'.stationnement = s.stationnement
s'.event = ajouter
}

pred Avancer[t:Train, s,s':State ]
{
t in (s.position).Int
some p : t.(s.position) |
			plus[p,1] not in Train.(s.position)
	and 	s'.position = s.position ++ t->plus[p,1]
s'.trains = s.trains
s'.stationnement = s.stationnement
s'.event = avancer
}

pred Garer[t:Train, s,s':State ]
{
t in (s.position).Int
t.(s.position) not in Train.(s.stationnement)
s'.trains = s.trains
s'.position = (Train-t) <: s.position
s'.stationnement = s.stationnement + t->t.(s.position)
s'.event = garer
}

pred Repartir[t:Train, s,s':State ]
{
t in (s.stationnement).Int
t.(s.stationnement) not in Train.(s.position)
s'.trains = s.trains
s'.position = s.position + t->t.(s.stationnement)
s'.stationnement = (Train-t) <: s.stationnement
s'.event = repartir
}

pred Transition[s,s':State]
{
some  t : Train, p: Int |
			Ajouter[t,p,s,s']
	or		Avancer[t,s,s']
	or		Garer[t,s,s']
	or		Repartir[t,s,s']
}

run test1
{
	some s1,s2:State |
		Init[s1] and
		Transition[s1,s2]
} for 3 but 2 State

run test2
{
TraceValide[] and
some s : State | #(s.position)>=2
} for 10 State, 3 Train

run test3
{
TraceValide[] and
some s : State, i : Int | #(s.position.i)>0 and #(s.stationnement.i)>0
} for 5 State, 3 Train

pred TraceValide[]
{
		Init[first]
and	all s : State-last |	let s' = next[s]	| Transition[s,s']
}

check invariant_trace {
	TraceValide[]
=>
	all s : State | Inv[s]
} for 5 State, 3 Train

check invariant_all_states
{
all s : State | Init[s] => Inv2[s]

all s,s' : State | Inv2[s] and Transition[s,s'] => Inv2[s']
} for 2 State, 3 Train

check invariant_all_states_sans_contrainte
{
all s : State | Inv2[s]
} for 2 State, 3 Train



check position_injective
{
all s : State |
			Inv2[s]
	=>	no t1, t2 : s.trains |
				{
				t1 != t2 
				t1.(s.position) = t2.(s.position) 
				some t1.(s.position) 
				some t2.(s.position)
				}
}

