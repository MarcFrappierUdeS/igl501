// retourne l'inverse d'un vecteur

predicate palindrome(a: array<int>, i : int)
   reads a
   requires i < a.Length
   requires a.Length > 0 
{
    forall x ::
        0 <= x <= i
      ==>
        a[x] == a[a.Length-1-x]
}

method EstPalindrome(a: array<int>) returns (r : bool)
   requires a.Length > 0
   ensures r <==> palindrome(a,a.Length-1)
{
   var i := 0;
   r := true;
   while i < (a.Length/2) 
      invariant 0 <= i <= a.Length
      invariant r <==> palindrome(a,i-1)
      decreases a.Length - i + 1
   {
      r := a[a.Length-i-1] == a[i];
      if ! r {return r;}
      i := i+1;
   }
}