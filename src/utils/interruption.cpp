#include "interruption.hpp"

void InterruptionHandler::Do(Interruption *interruption) {
	interruption->Print();
	abort();
}
