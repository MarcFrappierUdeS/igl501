open util/ordering[State] 

enum Event {init,add, del, transitive}

enum ELEM {a,b,c}

sig State {
  r : ELEM -> ELEM,
  event : Event
}

pred add[s,s' : State, x,y : ELEM]
{
x != y
x->y not in s.r
s'.r = s.r + x->y
s'.event = add
}

pred del[s,s' : State, x,y : ELEM]
{
x->y in s.r
s'.r = s.r - x->y
s'.event = del
}

pred transitive[s : State]
{
(s.r).(s.r) in s.r
}

pred Init[s:State]
{
no s.r
s.event = init
}

pred Transition[s,s':State]
{
  some x,y : ELEM |
    add[s,s',x,y] or
    del[s,s',x,y]
}

pred TraceValide[]
{
		Init[first]
and	all s : State-last |	let s' = next[s]	| Transition[s,s']
}

run coherence {
    TraceValide[]
}
for 3

pred inv[s : State]
{
no iden & s.r
}

check Inv {
all s : State | Init[s] => inv[s]
all s,s' : State | inv[s] and Transition[s,s'] => inv[s']
} for 2 State

check add_del {
		all x,y : ELEM, s1, s2, s3 : State | 
			      add[s1,s2,x,y]
        and add[s2,s3,x,y]
      =>
        s1.r = s3.r
}  for 3 State
