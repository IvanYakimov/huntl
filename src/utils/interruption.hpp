# ifndef __INTERRUPTION_HPP__
# define __INTERRUPTION_HPP__

#include <iostream>
#include <stdio.h>
#include <stdlib.h>

class Interruption {
public:
	//TODO implement std::function<> template
	virtual void Print() = 0;
	virtual ~Interruption() = 0;
};

class InterruptionHandler {
public:
	static void Do(Interruption *interruption);
};

# endif /* __INTERRUPTION_HPP__ */
