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

	class Array;
	using ArrayPtr = std::shared_ptr<Array>;
	class Array : public Solution {
	public:
		Array();
		void PushBack(SolutionPtr value);
		SolutionPtr GetElement(unsigned index);
		static ArrayPtr Create();
		unsigned GetSize();
	private:
		std::vector<SolutionPtr> val_list_;
	};

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
