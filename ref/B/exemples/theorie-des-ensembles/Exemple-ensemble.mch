MACHINE ExempleEnsemble
SETS
 ID={aa,bb}
CONSTANTS A, B, multiple3, plusPetit, succM
PROPERTIES
  A = 0..2
& B = 2..4
& multiple3 = { x | x : NAT & #y.(y : NAT & x = y * 3)}
& plusPetit = { x,y | x : NAT & y : NAT & x < y }
& succM = { x,y | x : 	 & y : NAT & y = x+1 }
END

