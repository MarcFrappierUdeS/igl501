// retourne la position j d'un élément minimal du vecteur a
// démarre à i = 1, avec post-incrémentation

method Minimum(a: array<int>) returns (j : int)
   requires a.Length > 0
   ensures 0 <= j < a.Length
   ensures forall k :: 0 <= k < a.Length ==> a[j] <= a[k]
{
   var i := 1;
   j := 0;
   while i < a.Length
      invariant 0 <= i <= a.Length
      invariant 0 <= j < a.Length
      invariant forall k :: 0 <= k < i ==> a[j] <= a[k]
      decreases a.Length - i
   {
      if a[i] < a[j] { j := i; }
      i := i+1;
   }
}