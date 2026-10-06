function fib(n: nat): nat
{
   if n == 0 then 0 else
   if n == 1 then 1 else
                  fib(n - 1) + fib(n - 2)
}

method ComputeFib(n: nat) returns (b: nat)
   ensures b == fib(n)
{
   var i := 0;
   var c := 1;
       b := 0;
   while i < n
      invariant 0 <= i <= n
      invariant c == fib(i + 1)
      invariant b == fib(i)
      decreases n-i
   {
      b, c := c, b+c;
      i := i + 1;
   }
}