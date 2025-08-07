// retourne la somme des éléments d'un vecteur de la postion 0 à i
function sum(a: array<int>, i : int): int
  reads a 
{
  if i < 0 || i >= a.Length then 0 else  a[i] + sum(a,i-1)
}

method Somme(a: array<int>) returns (s : int)
   requires a.Length > 0
   ensures s == sum(a,a.Length-1)
{
   var i := 0;
   s := a[0];
   assert s == sum(a,0);
   while i < a.Length-1
      invariant 0 <= i <= a.Length-1
      invariant s == sum(a,i)
      decreases a.Length - i
   {
      i := i+1;
      s := s + a[i];
   }
}