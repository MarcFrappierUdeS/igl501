/* Library
 * Author∈ Fama
 * Creation date∈ mer. juin 2 2010
 */
MACHINE Library
/*
  Specification of a library system
  University of Sherbrooke
  First version
  Eric Gaudet∈ July 21, 2009
  Modified by
  Marc Frappier and Benoit Fraikin∈ May 06, 2010 Benoit Fraikin∈ June 01, 2010
  Amel Mammar
 */

  DEFINITIONS
    BOOK_IS_NOT_RESERVED(bo) == (reservation(bo) = [])
  ; BOOK_IS_RESERVED(bo) == (reservation(bo) /= [])
  ; MEMBER_HAS_NO_RESERVATION(me) ==(me∉ran(union(ran(reservation))))
  ; Indice(bo, me)== (reservation(bo))⁻¹(me)
  ;

SETS
    MEMBER = {m1,m2,m3}
  ; BOOK = {b1,b2,b3}

CONCRETE_CONSTANTS
  /* Maximum of books a member can borrow */
  maxNbLoans

PROPERTIES
  maxNbLoans = 2

VARIABLES
    loan
  , member
  , book
  ,reservation

INVARIANT
    member ⊆ MEMBER
  ∧ book ⊆ BOOK
  ∧ /* a book can be borrowed by at most one member */
    loan ∈ book ⇸ member 
  ∧ /* A member can't borrow more than the maxNbLoans of the system */
    ∀ mm . ( mm ∈ member ⇒ card ( loan ▷ { mm } ) ≤ maxNbLoans )
  ∧ /* a book has a list of reservations, without duplicates */
    reservation ∈ book → iseq(member)

INITIALISATION
      loan := ∅
  ||  book := ∅
  ||  member := ∅
  ||  reservation := ∅
  
OPERATIONS

Acquire ( b ) =
PRE
    b ∈ BOOK
  ∧ b ∉ book
THEN
      book := book ∪ { b }
  ||  reservation(b):=[]
END
;

Discard ( b ) =
PRE
    b ∈ BOOK
  ∧ b ∈ book
  ∧ b ∉ dom ( loan )
  ∧ BOOK_IS_NOT_RESERVED(b)
THEN
    book := book - { b }||
    reservation := {b} ⩤ reservation  /* Update reservation after discarding a book  **** Fama*/
   
END
;

Join ( m ) =
PRE
    m ∈ MEMBER
  ∧ m ∉ member
THEN
    member := member ∪ { m }
END
;

Leave ( m ) =
PRE
    m ∈ MEMBER
  ∧ m ∈ member
  ∧ m ∉ ran(loan)
  ∧ MEMBER_HAS_NO_RESERVATION(m)
THEN
  member := member - { m }
END
;


Lend ( m , b ) =
PRE
    m ∈ MEMBER
  ∧ m ∈ member
  ∧ b ∈ BOOK
  ∧ b ∈ book
  ∧ b ∉ dom ( loan )
  ∧ BOOK_IS_NOT_RESERVED(b)
  ∧ card ( loan ▷ { m } ) < maxNbLoans
THEN
  loan ( b ) := m
END
;

Renew ( m , b ) =
PRE
    m ∈ MEMBER
  ∧ b ∈ BOOK
  ∧ m ∈ member
  ∧ b ∈ book
  ∧ b ↦ m ∈ loan
  ∧ BOOK_IS_NOT_RESERVED(b)
THEN
  skip
END
;

Reserve ( m , b ) =
PRE
    m ∈ MEMBER
  ∧ b ∈ BOOK
  ∧ m ∈ member
  ∧ b ∈ book
  ∧ m ∉ ran(reservation(b))
  ∧ b ↦ m ∉ loan
  ∧ (
      b ∈ dom ( loan )
    or
      BOOK_IS_RESERVED(b)
    )
THEN
    reservation := reservation <+ { b ↦ ((reservation(b) <- m)) } 
END
;

Return ( b ) =
PRE
    b ∈ BOOK
  ∧ b ∈ book
  ∧ b ∈ dom ( loan )
THEN
  loan := { b } ⩤ loan
END
;

/* Borrow the book m which has been reserved by b */
Take ( m , b ) =
PRE
    m ∈ MEMBER
  ∧ b ∈ BOOK
  ∧ m ∈ member
  ∧ b ∈ book
  ∧ b ∉ dom ( loan )
  ∧ card ( loan ▷ { m } ) < maxNbLoans
  ∧ reservation(b) ≠ []
  ∧ first(reservation(b)) = m
THEN
      loan ( b ) := m
  ||  reservation := reservation <+ {b ↦ tail(reservation(b))}        
END
;

Cancel ( m , b ) =
PRE
    m ∈ MEMBER
  ∧ m ∈ member
  ∧ b ∈ BOOK
  ∧ b ∈ book
  ∧ b ∈ dom(reservation)
  ∧ m ∈ ran(reservation(b))
THEN
    reservation(b) :=
        ((1..Indice(b,m)-1) ◁ reservation(b))
      ∪ (λii.(ii ∈ Indice(b,m)..size(reservation(b))-1
          | reservation(b)(ii+1)))
END

END

