// z est le maximum de x et y
function max(x : int, y : int) : int
{
    if x >= y then x else y
}

method Maximum(x1 : int, x2 : int, x3 : int) returns (z : int)
   ensures z == max(x3,max(x1,x2))
{
    if x1 >= x2
        {
        if x1 >= x3
            {z := x1;}
        else
            {z := x3;}
        }
    else
        if x2 >= x3
            {z := x2;}
        else
            {z := x3;}
}