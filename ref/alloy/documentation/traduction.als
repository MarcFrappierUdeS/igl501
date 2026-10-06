open util/ordering[State] 
abstract sig A {}
one sig a1,a2 extends A {}
sig B {}
one sig b extends B {}
sig B1 in B {f: one B}
fact
{ some x : B1 | x.f = b }

sig State {
a3  : A,
A1 : set A,
g  : A1 -> A1
}

pred Invariant[s : State]
{
one s.a3    // a3 est un scalaire
s.a3 in s.A1
s.A1 in A
s.g in s.A1 -> lone s.A1
some y : s.A1 | s.a3 -> y in s.g
}

pred Init[s:State]
{
s.a3 = a1
s.A1 = a1+a2
s.g = a1 -> a1
}

pred add_g[x : A, s,s' : State]
{
x in s.A1
s'.g = s.g ++ x -> x
s'.a3 = s.a3    // no change
s'.A1 = s.A1    // no change
}

pred TraceValide[]
{
		Init[first]
and	all s : State-last |	let s' = next[s]	|
        some x : A | add_g[x,s,s']
}

run test1 {TraceValide[]} for 1

run test2 {
	  TraceValide[]
and some s1,s2 : State | add_g[a2,s1,s2]
} for 3 but exactly 4 State

run test3 {
    Init[first]
and let s = next[first]	| add_g[a2,first,s]
} for 3 but exactly 2 State

check CheckInv {
all s : State | Init[s] => Invariant[s]
all x : A, s,s' : State |
       Invariant[s] and add_g[x,s,s']
    =>
       Invariant[s']
} for 2 but 2 State










