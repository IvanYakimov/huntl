int f (int a, int b)
{
  return a + b / 2;
}

int g (int x)
{
  if (x < 0)
    return -1;
  else
    return 1;
}

int main ()
{
  f (1, 2);
  g (100);
}

