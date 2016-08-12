#ifndef __SOLUTION_HPP__
#define __SOLUTION_HPP__

#include <memory>
#include <list>
#include <vector>
#include <iostream>

#include "meta-int.hpp"
#include "object.hpp"
#include "creatable.hpp"

namespace interpreter {
	using interpreter::MetaInt; using interpreter::MetaIntRef; using std::ostream;
	class Solution {
	public:
		virtual ~Solution(){}
	};
	using SolutionPtr = std::shared_ptr<Solution>;

	class Integer : public Solution {
	public:
		Integer(MetaIntRef value);
		const MetaIntRef Get() const;
		virtual ~Integer(){}
		static SolutionPtr Create(MetaIntRef value);
	private:
		MetaInt value_;
	};
	using IntegerPtr = std::shared_ptr<Integer>;

	class Array : public Solution {
	public:
		Array();
		void PushBack(MetaIntRef value);
		MetaIntRef GetElement(unsigned index);
		static SolutionPtr Create();
	private:
		std::vector<MetaInt> val_list_;
	};
	using ArrayPtr = std::shared_ptr<Array>;

	class Pointer : public Solution {
	public:
		Pointer(SolutionPtr target);
		SolutionPtr Dereference();
		static SolutionPtr Create(SolutionPtr target);
	private:
		SolutionPtr target_;
	};
	using PointerPtr = std::shared_ptr<Pointer>;

	using SolutionList = std::list<SolutionPtr>;
	using SolutionListPtr = std::shared_ptr<SolutionList>;
}

#endif
