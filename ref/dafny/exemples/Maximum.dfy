// z est le maximum de x et y
function max(x : int, y : int, z : int): bool
{
  z >= y && z >= x && (z==x || z==y)
}

method Maximum(x : int, y : int) returns (z : int)
   ensures max(x,y,z)
{
   if x < y {z := y;} else {z := x;}
}