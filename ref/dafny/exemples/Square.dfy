method Square(x: int) returns (y: int)
{
  y := x * x;
}

method Main()
{
  var z := Square(5);
  print z, "\n";
}