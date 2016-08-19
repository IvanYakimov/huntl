#include "solution-record.hpp"

namespace interpreter {
	using solver::SharedExpr;
	SolutionRecord::SolutionRecord(SolutionPtr solution, SharedExpr variable, MetaIntRef value) :
		solution_(solution),
		variable_(variable){
		value_ = value;
		assert ((solution_ != nullptr) and (not variable.isNull()));
	}

	void Print(SolutionRecordListPtr the_list, std::ostream& file) {
		file << "solution record [" << the_list->size() << "]: ";
		for (auto it = the_list->begin(); it != the_list->end(); it++) {
			file << (*it)->variable_ << " := ";
			file << (*it)->value_ << "; ";
		}
		file << std::endl;
		std::flush(std::cerr);
	}
}
