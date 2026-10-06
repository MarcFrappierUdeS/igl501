open util/ordering[State] 
enum Event {a,b,c}

sig State {
event : Event
}

run test1 {
first.event = a
first.next.event = b
first.next.next.event = c
} for 3 State
