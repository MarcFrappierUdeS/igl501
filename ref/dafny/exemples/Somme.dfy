// retourne la somme des éléments d'un vecteur de la postion 0 à i
function sum(a: array<int>, i : int): int
  reads a 
{
  if i < 0 || i >= a.Length then 0 else  a[i] + sum(a,i-1)
}

method Somme(a: array<int>) returns (s : int)
   ensures s == sum(a,a.Length-1)
{
   var i := 0;
   s := 0;
   while i < a.Length
      invariant 0 <= i <= a.Length
      invariant s == sum(a,i-1)
      decreases a.Length - i
   {
      s := s + a[i];
      i := i+1;
   }
}