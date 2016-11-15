# README #
Copyrigth 2016 Ivan Yakimov

## About ##
Huntl is a test generation tool based on dynamic symbolic exectuion.
It relies on:
* LLVM compiler infrastructure
* CVC4 solver.

## Background ##
The symbolic execution (in context of test generation) was [invited](https://academic.microsoft.com/#/detail/2101512909) by King in 1976.

The closest systems to the Huntl are [EXE](https://academic.microsoft.com/#/detail/31771106) and [KLEE](https://klee.github.io/).

Also it provides a new (in context of symbolic exectuion) method of readability optimization (*conceptually*) like [this](https://academic.microsoft.com/#/detail/31771106).

## Examples ##
We have tested this program against 12 Linux functions for [string processing](https://github.com/torvalds/linux/blob/master/lib/string.c) with **no modifications**. 
###Target###
```
int strcmp(const char *cs, const char *ct)
{
	unsigned char c1, c2;

	while (1) {
		c1 = *cs++;
		c2 = *ct++;
		if (c1 != c2)
			return c1 < c2 ? -1 : 1;
		if (!c1)
			break;
	}
	return 0;
}
```
###Unoptimized output###
```
strcmp: &""{\0,\0,\0,\0,\0,\0} &""{\0,\0,\0,\0,\0,\0} :=> 0
strcmp: &"\x02"{\0,\0,\0,\0,\0} &"\x02"{\0,\0,\0,\0,\0} :=> 0
strcmp: &"\x02\x01"{\0,\0,\0,\0} &"\x02\x01"{\0,\0,\0,\0} :=> 0
strcmp: &"\x02\x01\x01"{\0,\0,\0} &"\x02\x01\x01"{\0,\0,\0} :=> 0
strcmp: &"\x02\x01\x01\x01"{\0,\0} &"\x02\x01\x01\x01"{\0,\0} :=> 0
strcmp: &"\x02\x01\x01\x01\x01"{\0} &"\x02\x01\x01\x01\x01"{\0} :=> 0
strcmp: &"\x02\x01\x01\x01\x014"{\0} &"\x02\x01\x01\x01"{\0,\0} :=> 1
strcmp: &"\x02\x01\x01\x01"{\0,\0} &"\x02\x01\x01\x01\x01"{\0} :=> -1
strcmp: &"\x02\x01\x01\x014"{\0,\0} &"\x02\x01\x01"{\0,\0,\0} :=> 1
strcmp: &"\x02\x01\x01"{\0,\0,\0} &"\x02\x01\x01\x01"{\0,\0} :=> -1
strcmp: &"\x02\x01\x014"{\0,\0,\0} &"\x02\x01"{\0,\0,\0,\0} :=> 1
strcmp: &"\x02\x01"{\0,\0,\0,\0} &"\x02\x01\x01"{\0,\0,\0} :=> -1
strcmp: &"\x02\x014"{\0,\0,\0,\0} &"\x02"{\0,\0,\0,\0,\0} :=> 1
strcmp: &"\x02"{\0,\0,\0,\0,\0} &"\x02\x01"{\0,\0,\0,\0} :=> -1
strcmp: &"\x014"{\0,\0,\0,\0,\0} &"\x01"{\0,\0,\0,\0,\0} :=> 1
strcmp: &""{\0,\0,\0,\0,\0,\0} &"\x01"{\0,\0,\0,\0,\0} :=> -1
```
##vs.##
###Optimized one###
```
strcmp: &""{\0,p,i,m,s,\0} &""{\0,p,e,l,a,\0} :=> 0
strcmp: &"w"{\0,p,w,h,\0} &"w"{\0,p,i,b,\0} :=> 0
strcmp: &"jj"{\0,p,t,\0} &"jj"{\0,p,i,\0} :=> 0
strcmp: &"epp"{\0,p,\0} &"epp"{\0,p,\0} :=> 0
strcmp: &"enok"{\0,\0} &"enok"{\0,\0} :=> 0
strcmp: &"nanty"{\0} &"nanty"{\0} :=> 0
strcmp: &"xuwet"{\0} &"xuwea"{\0} :=> 1
strcmp: &"mnlri"{\0} &"mnlru"{\0} :=> -1
strcmp: &"biuyc"{\0} &"biugr"{\0} :=> 1
strcmp: &"ripfn"{\0} &"ripwe"{\0} :=> -1
strcmp: &"msosm"{\0} &"mskrh"{\0} :=> 1
strcmp: &"bakvo"{\0} &"baste"{\0} :=> -1
strcmp: &"taupt"{\0} &"tOpmg"{\0} :=> 1
strcmp: &"ychmp"{\0} &"yhies"{\0} :=> -1
strcmp: &"qeutu"{\0} &"cpalp"{\0} :=> 1
strcmp: &"xeptv"{\0} &"yngmb"{\0} :=> -1
```
As you can see, the optimized test suite is more readable and *less* expensive in terms of the "*Human Oralce Cost*" than unoptimized one.

Note: this output can be used to produce test-suite in the C language, as here: [Huntl Prototype](https://github.com/IvanYakimov/huntl-prototype)
