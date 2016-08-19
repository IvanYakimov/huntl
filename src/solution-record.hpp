#ifndef __SOLUTION_RECORD_HPP__
#define __SOLUTION_RECORD_HPP__

#include "solution.hpp"
#include "expr.hpp"
#include "meta-int.hpp"

#include <list>
#include <memory>
#include <cassert>
#include <iostream>

namespace interpreter {
	class SolutionRecord {
	public:
		SolutionRecord(SolutionPtr solution, solver::SharedExpr variable, MetaIntRef value);
		~SolutionRecord();
		interpreter::SolutionPtr solution_;
		solver::SharedExpr variable_;
		interpreter::MetaInt value_;
	};
	using SolutionRecordPtr = std::shared_ptr<SolutionRecord>;
	using SolutionRecordList = std::list<SolutionRecordPtr>;
	using SolutionRecordListPtr = std::shared_ptr<SolutionRecordList>;
	void Print(SolutionRecordListPtr the_list, std::ostream& file);
}

#endif











