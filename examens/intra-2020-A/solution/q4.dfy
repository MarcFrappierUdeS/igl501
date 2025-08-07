// vérifie si tous les éléments d'un vecteur sont strictement positifs
predicate positif(a: array<int>, i : int)
   reads a
   requires i < a.Length
   requires a.Length > 0 
{
    forall x ::
        0 <= x <= i
      ==>
        a[x] > 0
}

method EstPositif(a: array<int>) returns (r : bool)
   requires a.Length > 0
   ensures r <==> positif(a,a.Length-1)
{
   var i := 0;
   r := true;
   while i < a.Length && r
      invariant 0 <= i <= a.Length
      invariant r <==> positif(a,i-1)
      decreases a.Length - i
   {
      r := r && a[i] > 0;
      i := i+1;
   }
}

method Main()
{
  var a := new int[3];
  a[0] := 4;
  a[1] := -1;
  a[2] := 4;
  var p : bool := EstPositif(a);
  print "EstPositif == ", p, "\n";
}