open util/ordering[State] 

enum Event {init,call,accept,decline,cancel,terminate}

sig User{}

sig State
{
	libre : set User,
	appelant : set User -> User,
	connecte : User -> User,
	event : Event
}

pred Init [S:State]
{
	S.libre=User
	no S.appelant
	no S.connecte
	S.event = init
}
 
pred Call[u1,u2:User,S,S':State]
{
u1 != u2
u1 in S.libre
u2 in S.libre
S'.libre = S.libre - (u1+u2)
S'.appelant = S.appelant + u1->u2
S'.connecte = S.connecte
S'.event = call
}

pred Accept[u2:User,S,S':State]
{
some u1 : User | {
	u1->u2 in S.appelant
	S'.libre = S.libre
	S'.appelant = S.appelant - u1->u2
	S'.connecte = S.connecte + u1->u2
	}
S'.event = accept
}

pred Decline[u2:User,S,S':State]
{
some u1 : User | {
	u1->u2 in S.appelant
	S'.libre = S.libre + (u1+u2)
	S'.appelant = S.appelant - u1->u2 
	S'.connecte = S.connecte
	}
S'.event = decline
}

pred Cancel[u1:User,S,S':State]
{
some u2 : User | {
	u1->u2 in S.appelant
	S'.libre = S.libre + (u1+u2)
	S'.appelant = S.appelant - u1->u2 
	S'.connecte = S.connecte
	}
S'.event = cancel
}

pred Terminate[u1:User,S,S':State]
{
some u2 : User | {
	u1->u2 in S.connecte or u2->u1 in S.connecte
	S'.libre = S.libre + (u1+u2)
	S'.appelant = S.appelant 
	S'.connecte = S.connecte - (u1->u2 + u2->u1)
	}
S'.event = terminate
}

pred Inv[S:State]
{
S.appelant in User lone -> lone User
S.connecte in User lone -> lone User
no (S.libre & (S.appelant.User + User.(S.appelant)))
no (S.libre & (S.connecte.User + User.(S.connecte)))
no ((S.connecte.User + User.(S.connecte)) & (S.appelant.User + User.(S.appelant)))
no (iden & ^(S.appelant))
no (iden & ^(S.connecte))
no (S.connecte.User & User.(S.connecte))
no (S.appelant.User & User.(S.appelant))
}

pred Transition[S,S':State]
{
some u1,u2:User |
		Call[u1,u2,S,S']
	or Accept[u1,S,S']
	or Decline[u1,S,S']
	or Cancel[u1,S,S']
	or Terminate[u1,S,S']
}

check Invariant_Init
{
	all S : State | Init[S] => Inv[S]
}  for 1 State, 3 User

check Invariant_Transition
{
	all S,S':State |
			Inv[S] and Transition[S,S'] =>	Inv[S']
}  for 2 State, 3 User

check Invariant_Both
{
	all S : State | Init[S] => Inv[S]
	all S,S':State | Inv[S] and Transition[S,S'] =>	Inv[S']
}  for 2 State, 3 User

pred TraceValide[]
{
		Init[first]
and	all s : State-last |	let s' = next[s]	| Transition[s,s']
}

run showTrace
{
TraceValide[] and some S : State | # S.connecte = 2
} for 9 State, 4 User
