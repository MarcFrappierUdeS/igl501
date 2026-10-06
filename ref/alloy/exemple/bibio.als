open util/ordering[State] 

one sig Constants
{
	maxNbLoans : Int
}
{
	maxNbLoans = 7
}

enum Event {init,acquire,discard,join,leave,lend,renew,return,reserve,take,cancel}

sig Book{}

sig Member{}

sig State
{
	members : set Member,
	books : set Book,
	loan:  (Book ->  Member),
	reservation : (seq Member) -> Book,
	event : Event
}

/* =================================
		=  List of no change predicates =
		= They are used in action to describe which state =
		= variables remain unchanged = 
===================================*/

pred NoChangeBooks[s,s':State]
{
	s.books = s'.books
}

pred NoChangeMembers[s,s':State]
{
	s.members = s'.members
}

pred NoChangeLoan[s,s':State]
{
	s.loan = s'.loan
}

pred NoChangeReservation[s,s':State]
{
	s.reservation = s'.reservation
}

/*----------------
    Initialisation
------------------*/
pred Init [s:State]
{
	no s.books
	no s.members
	no s.loan
	no s.reservation
	s.event = init
}

/*--------- ----------
    Acquire
-------------------*/
pred CanBeAcquire[s:State,b:Book]
{
	no(b & s.books) // verify that b is not in the Library
}
 
pred Acquire[b:Book,s,s':State]
{
	----Preconditon-------
	CanBeAcquire[s,b]

	-----Postcondition-------
	s'.books = s.books  + b // add the b in  the set of books
	s'.event = acquire
	
	----NoChange-----
	NoChangeMembers[s,s']
	NoChangeLoan[s,s']
	NoChangeReservation[s,s']
}

/*--------- ----------
    Join
-------------------*/
pred CanJoin[m:Member,s:State]
{
	no (m &  s.members)// m does not exist in the Library.   
}

pred Join[m:Member,s,s':State]{

	----Precondition-----
	CanJoin[m,s]

	-----Postcondition------
	s'.members = s.members + m// add the m in the set of members 
	s'.event = join
		
	------NoChange-----
	NoChangeBooks[s,s']
	NoChangeLoan[s,s']
	NoChangeReservation[s,s']
}

/*--------- ----------
    LEND
-------------------*/
pred CanLend[m:Member,b:Book,s:State]
{
	(b in s.books) and (m in s.members)  // b and m are in the Library 
  (#((s.loan).m) < Constants.maxNbLoans) //maxNbLoans is the number maximum of loans authorized 
//	all m':Member | no((s.loan).m' & b)// b is not lent
   no (b.(s.loan)) // b is not lent
	 no (s.reservation.b)// b not reserved

} 

pred Lend[m:Member,b:Book,s,s':State]
{

	-----Precondition------------
	CanLend[m,b,s]
	 
	----Postcondition-------------
	s'.loan = s.loan  + (b->m)   
	s'.event = lend
	
	----NoChange------------
	NoChangeBooks[s,s']
	NoChangeMembers[s,s']
	NoChangeReservation[s,s']
}

/*--------- ----------
    RESERVE
-------------------*/
pred CanReserve[m:Member,b:Book,s:State]
{
	(b in s.books and m in s.members ) // b and m are in the Library
//	one (b & ((s.loan).Member)) or (some (s.reservation.b))// the book is a borrowed 
  (b in (s.loan).Member) or (some (s.reservation.b))// the book is a borrowed 
  no (m & b.(s.loan)) //  m is not borrowing
	no (Int.(s.reservation.b) & m) //it can't be reserved more than once by the same member
}

pred Reserve[m:Member,b:Book,s,s':State]
{
	---- Precondition----
	CanReserve[m,b,s]

	------PostCondition-----
	s'.reservation.b = add[s.reservation.b,m]
	s'.event = reserve

	-----NoChange-------
	all b':Book - b | s'.reservation.b' = s.reservation.b'
	NoChangeBooks[s,s']
	NoChangeMembers[s,s']
	NoChangeLoan[s,s']
}

/*--------- ----------
    CANCEL
-------------------*/
pred CanCancel[m:Member,b:Book,s:State]
{

	(b in s.books and m in s.members ) // // b and m are in the Library
	 one (Int->m & (s.reservation.b))// b is reserved by m
}

pred Cancel[m:Member,b:Book,s,s':State]
{
	--------Preconditon---------------
	CanCancel[m,b,s]

	 --------Postconditon------------ 
	s'.reservation.b=delete[s.reservation.b,indsOf[s.reservation.b,m]]// delete m from the list of reservation of b
	s'.event = cancel
	
	------NoChange--------
	all b':Book - b | s'.reservation.b' = s.reservation.b'
	NoChangeBooks[s,s']
	NoChangeMembers[s,s']
	NoChangeLoan[s,s']
}

/*--------- ----------
    RETURN
-------------------*/
pred CanReturn[m:Member,b:Book,s:State]
{
	(b in s.books and m in s.members )
	one ((s.loan).m & b)  // b is already lent to m  
}

pred Return[m:Member,b:Book,s,s':State]
{
	----Precondition-----
	CanReturn[m,b,s]

	----PostConditon--------
	s'.loan=s.loan - (b ->m)	// delete the b->m from the set of loans 
	s'.event = return


	----NoChange--------
	NoChangeBooks[s,s']
	NoChangeMembers[s,s']
	NoChangeReservation[s,s']
}

/*--------------------
	TAKE
----------------------*/
pred CanTake[m:Member,b:Book,s:State]
{
	(b in State.books) and (m in s.members) // b and m are in the Library 
	(#((s.loan).m) < Constants.maxNbLoans) // maxNbLoans is the number maximum of lend authorized 
	(0 -> m) in (s.reservation.b) // m is first in the list  of reservation 
 	no (b.(s.loan)) // the book is not lent
}

pred Take[m:Member,b:Book,s,s':State]
{
	-----Preconditon-------
	CanTake[m,b,s]

	-----PostCondition-----
	s'.loan = s.loan  + (b->m) 
	s'.reservation.b = delete[s'.reservation.b,0]//delete m from the list of reservations of b
	s'.event = take
	
	-----NoChange-------
	all b':Book - b | s'.reservation.b' = s.reservation.b'
	NoChangeBooks[s,s']
	NoChangeMembers[s,s']
}

/*-----------------
		LEAVE
-------------------*/

pred CanLeave[m:Member,s:State]
{
	m in s.members
	no (s.loan.m) // m is not in the lent list
 	no( Int.(s.reservation.Book) & m)// m has no reseravation
}

pred Leave[m:Member,s,s':State]
{ 	
	------Preconditon-------
	CanLeave[m,s]

	------Postconditon------
	s'.members = s.members - m
	s'.event = leave

	----NoChange---------
	NoChangeLoan[s,s']
	NoChangeReservation[s,s']
  NoChangeBooks[s,s']	
}

/*-----------------
		DISCARD
-------------------*/
pred CanDiscard[b:Book,s:State]
{
	b in s.books
	no (b.(s.loan))
	no ((s.reservation.b) )
}

pred Discard[b:Book,s,s':State]
{
	------Precondition-------
	CanDiscard[b,s]
	------Postconditon--------
	s'.books = s.books - b
	s'.event = discard
	-----NoChange-------
	NoChangeLoan[s,s']
	NoChangeReservation[s,s']
 	NoChangeMembers[s,s']
}

/*--------------------
		RENEW
----------------------*/
pred CanRenew[m:Member,b:Book,s:State]
{
	one (b.(s.loan) & m) // b is already borrowed by m
	isEmpty [s.reservation.b]  //b has no reservation 
}

pred Renew[m:Member,b:Book,s,s':State]
{
	------Preconditon-------
	CanRenew[m,b,s]

	------Postconditon--------
	s'.event = renew

	------NoChange-----
	NoChangeBooks[s,s']
	NoChangeMembers[s,s']
	NoChangeLoan[s,s']
	NoChangeReservation[s,s']
}

pred reservedBy[bo:Book,me:Member,s:State]
{
me in Int.(s.reservation.bo)
}

pred borrowedBy[bo:Book,me:Member,s:State]
{
bo->me in s.loan
}

pred reservedBefore[bo:Book,me1,me2:Member,s:State]
{
(s.reservation.bo).idxOf[me1] < (s.reservation.bo).idxOf[me2]
}

pred LoanLimitNotExceeded[s:State]
{
  all m: Member |  (#((s.loan).m) <= Constants.maxNbLoans)
}

pred LoanIsAFunction[s:State]
{
// all b : Book |  lone (b ->Member &  (s.loan)) 
s.loan in Book -> lone Member
}

pred ReservationIsInjective[s:State]
{
//all m:Member,b:Book | lone (Int->m & (s.reservation.b))
all b:Book | s.reservation.b in Int lone -> lone Member
}

pred DomainOfLoanIsBook[s:State]
{
s.loan.Member in s.books
}

pred Inv[s:State]
{
LoanLimitNotExceeded[s]
LoanIsAFunction[s]
DomainOfLoanIsBook[s]
ReservationIsInjective[s]
}

pred Transition[s,s':State]
{
some b:Book, m:Member |
		Lend[m,b,s,s']
	or Reserve[m,b,s,s']
	or Take[m,b,s,s']
	or Cancel[m,b,s,s']
	or Return[m,b,s,s']
	or Acquire[b,s,s']
	or Discard[b,s,s']
	or Join[m,s,s']
	or Leave[m,s,s']
	or Renew[m,b,s,s']
}

assert Invariant_Init
{
	all s : State | Init[s] => Inv[s]
}

check Invariant_Init for 1 State, 15 Member, 15 Book

assert Invariant_Transition
{
	all s,s':State |
			Inv[s] and Transition[s,s'] =>	Inv[s']
}

check Invariant_Transition for 2 State, 8 Member, 8 Book, 5 int

assert Invariant_Both
{
	(all s : State | Init[s] => Inv[s])
	(all s,s':State | Inv[s] and Transition[s,s'] =>	Inv[s'])
}

check Invariant_Both for 2 State, 8 Member, 8 Book, 5 int

pred TraceValide[]
{
		Init[first]
and	all s : State-last |	let s' = next[s]	| Transition[s,s']
}

// Trace avec au moins deux prêt
run showTrace
{
TraceValide[] and some s : State | #(s.loan) >= 2
} for 9 State, 3 Book, 2 Member

run showTrace_Reserve
{
TraceValide[] and #event.reserve >= 2 and no event.cancel
} for 8 State, 3 Book, 3 Member

// Trace avec un take précédé de deux reserve sans cancel
run showTrace_Take
{
TraceValide[]
some s : State 
  {
  s.event = take
  #((prevs[s]<:event).reserve) >= 2
  no (prevs[s]<:event.cancel)
  }
} for 9 State, 1 Book, 3 Member

// test d'une trace particulière
run test_take
{
some s0,s1,s2,s3,s4,s5,s6,s7,s8,s9 : State, m1, m2, m3 : Member, b : Book |
  {
  TraceValide[]
  Init[s0]
  Join[m1,s0,s1]
  Join[m2,s1,s2]
  Join[m3,s2,s3]
  Acquire[b,s3,s4]
  Lend[m1,b,s4,s5]
  Reserve[m2,b,s5,s6]
  Reserve[m3,b,s6,s7]
  Return[m1,b,s7,s8]
  Take[m2,b,s8,s9]
  }
} for 10 State, 1 Book, 3 Member
