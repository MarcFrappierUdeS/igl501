// retourne le produit des éléments d'un vecteur de la postion 0 à i
function prod(a: array<int>, i : int): int
  reads a 
{
  if i < 0 || i >= a.Length then 1 else  a[i] * prod(a,i-1)
}

method Produit(a: array<int>) returns (s : int)
   ensures s == prod(a,a.Length-1)
{
   var i := 0;
   s := 1;
   while i <= a.Length-1
      invariant 0 <= i <= a.Length
      invariant s == prod(a,i-1)
      decreases a.Length - i
   {
      s := s * a[i];
      i := i+1;
   }
}