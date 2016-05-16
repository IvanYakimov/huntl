# include "expr.hpp"

using std::function;

namespace solver
{
	BasicIntVal::~BasicIntVal() {
	}

	bool BasicIntVal::Equals (const Object& rhs) const {
		auto cmp = [] (const BasicIntVal &lhs, const BasicIntVal &rhs) -> bool {
				//return lhs.GetVal() == rhs.GetVal()
				assert(false && "not implemented");
			};
		return EqualsHelper<BasicIntVal>(*this, rhs, cmp);
	}

	std::string BasicIntVal::ToString() const {
		//return "bv" + to_string(GetWidth()) + " " + std::to_string(GetVal());
		assert(false && "not implemented");
	}

	Width BasicIntVal::GetWidth() const {
		return width_;
	}

	uint64_t BasicIntVal::GetUInt64() const {
	#if defined(_M_X64) || defined(__amd64__)
		uint64_t result = 0L;
		memcpy(&result, &value_, align_);
		return result;
	#else
	#error "on amd64 is supported"
	#endif
	}

	void BasicIntVal::SetUInt64(const uint64_t& val) {
	#if defined(_M_X64) || defined(__amd64__)
			memcpy(&value_, &val, align_);
	#else
	#error "on amd64 is supported"
	#endif
	}

	Var::Var (std::string name, BitVecWidth type) {
		name_ = name;
		type_ = type;
		id_ = id_cache_.Get();
	}

	Var::~Var() {
	}

	IndexCache<uint64_t> Var::id_cache_(1);

	bool Var::Equals(const Object& rhs) const {
		auto cmp = [] (const Var &lhs, const Var &rhs) -> bool {
			return lhs.name_ == rhs.name_
					and lhs.type_ == rhs.type_
					and lhs.id_ == rhs.id_;
		};
		return EqualsHelper<Var>(*this, rhs, cmp);
	}

	std::string Var::ToString() const {
		return "btv" + std::to_string(GetType()) + " " + GetName() + ":s" + std::to_string(id_);
	}
	std::string Var::GetName() const {return name_;}
	BitVecWidth Var::GetType() const {return type_;}
	void Var::Reset() { id_cache_.Reset(); }
}













