# README #
Copyrigth 2016 Ivan Yakimov

## About ##
Huntl is an automated code-based test generation tool.
It relies on Dynamic Symbolic Execution (DSE) to guide process of program evaluation along the set of desired paths. 
The technology behind it:
* LLVM compiler infrastructure
* CVC4 solver.

## The main feature

Modern advanced DSE generators tend to produce dozens of almost unreadable test cases. This tool provides test data optimization method that drastically improves readability of produced test inputs. You can check out article about this new method here: [in Russian](http://www.ispras.ru/proceedings/isp_28_2016_5/isp_28_2016_5_227/)

## Background
Symbolic Execution (in context of test generation) was [introduced](https://academic.microsoft.com/#/detail/2101512909) by King in 1976.

In terms of realization the closest systems to the Huntl are [EXE](https://academic.microsoft.com/#/detail/31771106) and [KLEE](https://klee.github.io/).

## Examples
We have tested this program against 12 Linux functions for [string processing](https://github.com/torvalds/linux/blob/master/lib/string.c) with **no modifications**. 

Let's say we have `strcmp` function as a target.
``` C
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

Before start generating test inputs we should feed the generator a test driver.
Test driver is a simple program that declares type of function arguments and its result.
The declaration has name `gen_<NAME>` where NAME is a name of the target function.
In case of strcmp we have declared `gen_strcmp`. 
First two arguments of `gen_strcmp` are the same as `strcmp`: `cs` and `ct`.
The last argument `res` has a return type of the target funciton.
This arg tells the DSE engine which type we expect to be returned from the target `strcmp`.

``` C
void gen_strcmp(const char *cs, const char *ct, int res);
```

The test driver also defines the way execution of the target function is approached.
First we put a restriction to the length of the input and output strings `s1` and `s2`.
Function `init_buff` intializes a fixed-length array of symbolic values.
So, each symbolic value inside `s1/s2` despite the null-termiator is not restricted to have any concrete value,
as they are symbolic values.
After the inputs initialization proceeds a call to the actual `strcmp` function.
The target `strcmp` function is called as it is - without any modifications in source code.
To produce test data `gen_strcmp` is called at the end of the test drive source code.

``` C
void test_strcmp() {
	const size_t len = 6;
	char s1[len], s2[len];
	init_buff(s1, len); init_buff(s2, len);
	int res = strcmp(s1,s2);
	gen_strcmp(s1,s2,res);
}
```

### Unoptimized output

In the output below each line represents test data leading program along a unique execution path.
As you can see it is hard to evaluate the meaning of each line.

``` Haskell
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

### Optimized one

``` Haskell
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
