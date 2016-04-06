#ifndef __STATE_HPP__
#define __STATE_HPP__

#include <stack>
#include <memory>
#include <string>
#include "../utils/index-cache.hpp"
#include "../utils/object.hpp"

namespace interpreter {
	class State;
	using StatePtr = std::shared_ptr<State>;
	using StateId = unsigned long;
	class State : public CRTP <State, Mutable> {
	public:
		State();
		~State();
		virtual bool Equals (const Object& rhs) const;
		virtual std::string ToString() const;
		virtual ObjectPtr Clone();
	private:
		StateId id_;
		static IndexCache<StateId> id_cache_;
	};
};

#endif /* __STATE_HPP__ */














