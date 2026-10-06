open util/ordering[State] 
enum Event {init,inc}

sig State {
x : Int,
event : Event
}

pred Init[s:State]
{
s.x = 0
s.event = init
}

pred Inc[s,s' : State]
{
s'.x = plus[s.x,1]
s'.event = inc
}

run test1 {
		Init[first]
and	all s : State-last |
    let s' = next[s] |
        Inc[s,s']
} for 3 State

pred Inv[s:State]
{
s.x >= 0 and s.x <= 1
}

check InvInit {
all s : State |
    Init[s] => Inv[first]
} for 1 State

check InvInc {
all s,s' : State |
       Inv[s] and Inc[s,s']
    =>
       Inv[s']
} for 2 State

pred IncSafe[s,s' : State]
{
s.x < 1
s'.x = plus[s.x,1]
s'.event = inc
}

check InvIncSafe {
all s,s' : State |
       Inv[s] and IncSafe[s,s']
    =>
       Inv[s']
} for 2 State

