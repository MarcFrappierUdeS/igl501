open util/ordering [R] as rs
open util/ordering [State] as st

enum Event {init,acquerir,liberer,stutter,deadlock}

sig P {} // Processus
sig R {} // Ressources

sig State {
  obj : P -> R,  // objectif : ressources à acquérir par un processus
  acq : P -> R,  // ressources acquises par le processus
  event : Event
}

/* Precondition de Acquerir */
pred AcquerirPre[p:P, r:R, s:State]
{

r in p.(s.obj)          // r est à acquérir
r not in P.(s.acq)      // r est libre
r = rs/min[p.(s.obj)]      // r est la plus petite ressource à acquérir dans l'objectif
}

pred Acquerir[p:P, r:R, s,s':State]
{
// précondition
AcquerirPre[p,r,s]

// postcondition
p.(s'.obj) = p.(s.obj)-r
p.(s'.acq) = p.(s.acq)+r
s'.event = acquerir 

// no change
all p' : P-p | p'.(s'.obj) = p'.(s.obj)
all p' : P-p | p'.(s'.acq) = p'.(s.acq)
}

/* Precondition de Liberer */
pred LibererPre[p:P, s:State]
{
// précondition
no p.(s.obj)          // toutes les ressources sont acquises
some p.(s.acq)
}

pred Liberer[p:P, s,s':State]
{
// précondition
LibererPre[p, s]

// postcondition
no p.(s'.acq)
s'.event = liberer

// no change
all p' : P | p'.(s'.obj) = p'.(s.obj)
all p' : P-p | p'.(s'.acq) = p'.(s.acq)
}

pred FinalState[s:State]
{
no s.obj
no s.acq
}

/* Il y a un deadlock quand ni acquerir ni liberer
   ne peuvent s'exécuter (ie, leur precondition est fausse)
   et qu'il reste des objectifs */
pred DeadlockState[s:State]
{
some s.obj
no p : P, r : R | (AcquerirPre[p,r,s] or LibererPre[p,s])
}

// permet de compléter la trace au besoin en ne faisant rien dans l'état final
pred Stutter[s,s':State]
{
FinalState[s]
FinalState[s']
s'.obj = s.obj
s'.acq = s.acq
s'.event = stutter 
}

// permet de compléter la trace au besoin en ne faisant rien en cas de deadlock
pred Deadlock[s,s':State]
{
DeadlockState[s]
DeadlockState[s']
s'.obj = s.obj
s'.acq = s.acq
s'.event = deadlock 
}

pred Init[s:State]
{
all p:P | some p.(s.obj) and no p.(s.acq)
s.event = init
}

pred Transition[s,s':State]
{
some p:P, r:R |
		 Acquerir[p,r,s,s']
	or Liberer[p,s,s']
  or Stutter[s,s']    // afin de compléter la trace
  or Deadlock[s,s']   // afin de compléter la trace en cas de deadlock
}

pred TraceValide[]
{
		Init[st/first]
and	all s : State-st/last |	let s' = st/next[s]	| Transition[s,s']
}

run show_trace
{
TraceValide[]

all p : P | some s : State | p.(s.acq) = R
//all p : P | p.(st/first.obj) = R
//some p:P | one  p.(st/first.obj)
} for 13 State, exactly 2 P,  exactly 2 R

check deadlock_free
{
  TraceValide[]
=>
  FinalState[st/last]
} for 13 State,  3 P,  3 R

pred Inv[s:State]
{
// une ressource ne peut être acquise par deux processus en même temps
~(s.acq) in R -> lone P // l'inverse de s.acq est une fonction
}

assert Invariant
{
	all s : State | Init[s] => Inv[s]
	all s,s':State |
			Inv[s] and Transition[s,s'] =>	Inv[s']
}
check Invariant for 2 State, 3 P, 3 R
