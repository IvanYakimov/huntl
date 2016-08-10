#ifndef __WRAPPER_HPP__
#define __WRAPPER_HPP__

#include "object.hpp"
#include "creatable.hpp"
#include <cassert>
#include <sstream>

namespace utils {
	template <typename T>
	bool _compare_(const T& lhs, const T& rhs) {
		return lhs == rhs;
	}

	template <typename T>
	std::ostream& _print_(std::ostream &os, const T& obj) {
		os << obj;
		return os;
	}

	template <class Base,
		class Target,
		std::ostream& (*Show)(std::ostream&, const Target&) = _print_<Target>,
		bool (*Compare)(const Target&, const Target&) = _compare_<Target>>
	class Wrapper : public Base {
	public:
		using TheWrapper = Wrapper<Base,Target,Show,Compare>;

		COMPARABLE(Wrapper);
		NONCOPYABLE(Wrapper);

		Wrapper(const Target& val) : val_(val) {}

		virtual ~Wrapper() {}

		// const Target& Get() const {
		const Target& Get() const {
			return val_;
		}

		virtual bool Equals (const Object& rhs) const { /*
			auto cmp = [] (const TheWrapper& l, const TheWrapper& r) -> bool {
				return Compare(l.Get(), r.Get());
			};
			return EqualsHelper<TheWrapper>(*this, rhs, cmp);
			*/
			return val_ == static_cast<const TheWrapper&>(rhs).Get();
		}

		virtual std::ostream& ToStream(std::ostream &os, const Object& obj) const {
			return Show(os, val_);
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
