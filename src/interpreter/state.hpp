#ifndef __STATE_HPP__
#define __STATE_HPP__

#include <stack>
#include <memory>
#include <iostream>
#include "../utils/index-cache.hpp"

namespace interpreter {
	class State;
	using StatePtr = std::shared_ptr<State>;
	using StateId = unsigned long;
	class State {
	public:
		State();
		~State();
		friend bool operator==(const State& lhs, const State& rhs);
		friend bool operator!=(const State& lhs, const State& rhs);
		bool operator==(const State& rhs);
		bool operator!=(const State& rhs);
		friend std::ostream& operator<<(std::ostream &os, const State& state);
	private:
		StateId id_;
		static IndexCache<StateId> state_cache_;
	};
};

#endif /* __STATE_HPP__ */
