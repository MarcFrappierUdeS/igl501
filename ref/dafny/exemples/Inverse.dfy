// retourne l'inverse d'un vecteur

predicate inverse(a: array<int>, b: array<int>, i : int)
   reads a
   reads b
   requires a.Length == b.Length
   requires 0 <= i <= a.Length
   requires a.Length > 0 
{
    forall x ::
        0 <= x <= i-1 
      ==>
        a[x] == b[a.Length-1-x]
}

method Inverser(a: array<int>,b : array<int>)
   requires a.Length > 0
   requires b.Length == a.Length
   modifies b
   ensures inverse(a,b,a.Length-1)
{
   var i := 0;
   while i < a.Length
      invariant 0 <= i <= a.Length
      invariant inverse(a,b,i)
      decreases a.Length - i
   {
      b[a.Length-i-1] := a[i];
      i := i+1;
   }
}