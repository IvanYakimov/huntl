#ifndef __SOLUTION_HPP__
#define __SOLUTION_HPP__

#include <memory>
#include <list>
#include <vector>
#include <iostream>

//#include "meta-int.hpp"
#include "object.hpp"
#include "creatable.hpp"
#include "holder.hpp"
#include "holder-helper.hpp"

namespace interpreter {
	using std::ostream; using memory::HolderPtr;
	class Solution {
	public:
		virtual ~Solution(){}
	};
	using SolutionPtr = std::shared_ptr<Solution>;

	class Integer;
	using IntegerPtr = std::shared_ptr<Integer>;
	class Integer : public Solution {
	public:
		Integer(HolderPtr value);
		const HolderPtr Get() const;
		bool IsChar();
		virtual ~Integer(){}
		static IntegerPtr Create(HolderPtr value);
	private:
		HolderPtr value_;
	};

	class Array;
	using ArrayPtr = std::shared_ptr<Array>;
	class Array : public Solution {
	public:
		Array();
		void PushBack(SolutionPtr value);
		SolutionPtr GetElement(unsigned index);
		static ArrayPtr Create();
		unsigned GetSize();
		bool IsString();
	private:
		std::vector<SolutionPtr> val_list_;
	};

	class Pointer;
	using PointerPtr = std::shared_ptr<Pointer>;
	class Pointer : public Solution {
	public:
		Pointer(SolutionPtr target);
		SolutionPtr Dereference();
		static PointerPtr Create(SolutionPtr target);
	private:
		SolutionPtr target_;
	};

	IntegerPtr ToInteger(SolutionPtr solution);

	using SolutionList = std::list<SolutionPtr>;
	using SolutionListPtr = std::shared_ptr<SolutionList>;
}

#endif
