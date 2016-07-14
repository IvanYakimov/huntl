int gcdr ( int a, int b ) {
  if ( b==0 ) 
	return a;
  else 
	return a + gcdr(a, b-1);
}

int target (int x, int y) {
	if (x > 0 && x < 100 && y > 0) 
		return gcdr(x,y);
	else
		return -1;
}
