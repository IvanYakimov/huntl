#ifndef __STATE_HPP__
#define __STATE_HPP__

namespace interpreter {
	class State;
	using StatePtr = std::shared_ptr<State>;
	using StateId = unsigned long;
	class State {
	public:
		friend bool operator==(const State& lhs, const State& rhs);
		friend bool operator!=(const State& lhs, const State& rhs);
		friend operator==(const State& rhs);
		friend operator!=(const State& rhs);
		friend std::stream& operator<<(std::stream &os, const State& state);
	private:
		StateId id_;
	};
};

#endif /* __STATE_HPP__ */
