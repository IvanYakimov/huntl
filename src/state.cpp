#include "state.hpp"

namespace interpreter {

	//TODO:
	IndexCache<StateId> State::id_cache_(0);

	State::State() {
		id_ = id_cache_.Get();
	}

	State::~State() {
		id_cache_.PushBack(id_);
	}

	bool State::Equals (const Object& rhs) const {
		auto cmp = [] (const State &lhs, const State &rhs) {
			return lhs.id_ == rhs.id_;
		};
		return EqualsHelper<State>(*this, rhs, cmp);
	}

	std::string State::ToString() const {
		return "state #" + std::to_string(id_);
	}

	ObjectPtr State::Clone() {
		throw std::logic_error("not implemented");
	}
};















