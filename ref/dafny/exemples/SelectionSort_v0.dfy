// Selection sort
// version v0
// la spécification vérifie seulement que le vecteur final est trié
// elle ne vérifie pas que le vecteur de sortie est une permutaiton du vecteur d'entrée
// (* la version v1 fait cette vérification *)

predicate sorted(a: array<int>, i : int, j : int)
   reads a
   requires a.Length > 0 
{
    forall k1,k2 ::
        0 <= k1 < k2 < a.Length && i <= k1 < k2 <= j
      ==>
        a[k1] <= a[k2]
}

// retourne la position d'un élément minimum dans a entre i et la fin du vecteur
method Minimum(a: array<int>, i : int) returns (j : int)
   requires a.Length > 0
   requires 0 <= i < a.Length
   ensures i <= j < a.Length
   ensures forall k :: i <= k < a.Length ==> a[j] <= a[k]
{
   var n := i;
   j := i;
   while n < a.Length
      invariant i <= n <= a.Length
      invariant i <= j < a.Length
      invariant forall k :: i <= k < n ==> a[j] <= a[k]
      decreases a.Length - n
   {
      if a[n] < a[j] { j := n; }
      n := n+1;
   }
}

method SelectionSort(a: array<int>, i : int)
   requires a.Length > 0
   modifies a
   ensures sorted(a,0,a.Length-1)
{
  var i := 0;
  while i < a.Length
    invariant sorted(a,0,i-1)
    invariant forall k1,k2 :: 0 <= k1 < i <= k2 < a.Length ==> a[k1] <= a[k2]
    invariant 0 <= i <= a.Length
    decreases a.Length - i
    {
      var j := Minimum(a,i);
      assert 0 <= j < a.Length;
      a[i],a[j] := a[j],a[i];
      i := i + 1;
    }
}
