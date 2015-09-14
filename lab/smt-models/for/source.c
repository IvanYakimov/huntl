int factorial (int n)
{
  int c, fact = 1;
  for (c = 1; c <= n; c++)
    fact = fact * c;
  return fact;
}
