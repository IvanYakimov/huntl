int target(int x, int y) {
	if (y == 0)
		return x;
	else return x + target(x, y-1);
}
