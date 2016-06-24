#ifndef __WRAPPER_HPP__
#define __WRAPPER_HPP__

#include "object.hpp"
#include <cassert>
#include <sstream>

namespace meta_smt {
	template <typename T>
	bool EqualOp(const T& lhs, const T& rhs) {
		return lhs == rhs;
	}

	template <typename T>
	std::string Show(const T& arg) {
		//std::stringstream ss;
		//std::cout << arg.toString();
		//return "";//std::string(ss.str());
		return "";
	}

	template <class Base,
		class Target,
		std::string (*Show)(const Target&) = Show<Target>,
		bool (*Compare)(const Target&, const Target&) = EqualOp<Target>>
	class Wrapper : public Base {
	public:
		using TheWrapper = Wrapper<Base,Target,Show,Compare>;

		COMPARABLE(Wrapper);
		PRINTABLE(Wrapper);
		NONCOPYABLE(Wrapper);

		Wrapper(const Target& val) : val_(val) {}

		virtual ~Wrapper() {}

		const Target& Get() const {
			return val_;
		}

		virtual bool Equals (const Object& rhs) const {
			auto cmp = [] (const TheWrapper& l, const TheWrapper& r) -> bool {
				return Compare(l.Get(), r.Get());
			};
			return EqualsHelper<TheWrapper>(*this, rhs, cmp);
		}

		virtual std::string ToString() const {
			return Show(val_);
		}

		static std::shared_ptr<Base> Create(const Target& val) {
			return utils::Create<Base, TheWrapper>(val);
		}

		static const Target& UnWrap(std::shared_ptr<Base> base) {
			assert (base != nullptr);
			auto res = std::dynamic_pointer_cast<TheWrapper>(base);
			assert (res != nullptr);
			return res->Get();
		}

	private:
		Target val_;
	};
}

#endif