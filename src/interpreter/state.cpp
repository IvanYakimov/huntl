#include "state.hpp"

namespace interpreter {
	State::State() {
		id_ = state_cache_.Get();
	}

	State::~State() {
		state_cache_.PushBack(id_);
	}

	bool State::operator ==(const State& rhs) {
		return *this == rhs;
	}

	bool State::operator !=(const State& rhs) {
		return not (*this == rhs);
	}

	bool operator==(const State& lhs, const State& rhs) {
		return lhs.id_ == rhs.id_;
	}

	bool operator!=(const State& lhs, const State& rhs) {
		return not (lhs == rhs);
	}
};
