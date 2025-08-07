open util/ordering [State] as st

enum Event {init, creer, term, aff, lib}

sig Processus {}

sig Processeur {}

sig State {
	processus : set Processus,
  affectes : Processus -> Processeur,  // processus affecté a un processeur
  aEteaffectes : set Processus,
  event : Event
}

pred Creer[p:Processus, s,s':State]
{
// précondition
p not in (s.processus)

// postcondition
s'.processus = s.processus + p
s'.event = creer 

// no change
s'.affectes = s.affectes
s'.aEteaffectes = s.aEteaffectes
}

pred Term[p:Processus, s,s':State]
{
// précondition
p in s.processus
p in s.aEteaffectes
p not in s.affectes.Processeur

// postcondition
s'.processus = s.processus - p
s'.aEteaffectes = s.aEteaffectes - p
s'.event = term 

// no change
s'.affectes = s.affectes
}

pred Aff[p:Processus, r:Processeur, s,s':State]
{
// précondition
p in (s.processus)
p not in s.affectes.Processeur
r not in Processus.(s.affectes)

// postcondition
s'.affectes = s.affectes + p->r
s'.aEteaffectes = s.aEteaffectes + p
s'.event = aff

// no change
s'.processus = s.processus
}

pred Lib[p:Processus, r:Processeur, s,s':State]
{
// précondition
p in (s.processus)
p->r in s.affectes

// postcondition
s'.affectes = s.affectes - p->r
s'.event = lib

// no change
s'.processus = s.processus
s'.aEteaffectes = s.aEteaffectes
}

pred Init[s:State]
{
no s.processus
no s.affectes
no s.aEteaffectes
s.event = init
}

pred Transition[s,s':State]
{
some p:Processus, r:Processeur |
		 Creer[p,s,s']
	or Term[p,s,s']
  or Aff[p,r,s,s']
  or Lib[p,r,s,s']
}

pred TraceValide[]
{
		Init[st/first]
and	all s : State-st/last |	let s' = st/next[s]	| Transition[s,s']
}

run PeutTerminer
{
TraceValide[]
all p : Processus | some s,s' : State |s' = st/next[s] and Term[p,s,s']
} for 11 State, exactly 2 Processus, exactly 2 Processeur

pred Inv[s:State]
{
s.aEteaffectes in s.processus
s.affectes in Processus lone -> lone Processeur
}

check UnSeul 
{
	all s : State | Init[s] => Inv[s]
	all s,s':State |
			Inv[s] and Transition[s,s'] =>	Inv[s']
}
for 2 State, 3 Processus, 3 Processeur

check AffTerm
{
   TraceValide[]
=>
   all p : Processus | some s,s' : State |
       Term[p,s,s']
     =>
       some s1,s2 : st/prevs[s], r : Processeur |
         Aff[p,r,s1,s2]
} for 11 State, exactly 2 Processus, exactly 2 Processeur
