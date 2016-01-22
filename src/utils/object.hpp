#ifndef __OBJECT_HPP__
#define __OBJECT_HPP__

# include <memory>
# include <string>

class Object : public std::enable_shared_from_this<Object> {
public:
	virtual ~Object() {}
	virtual const std::string ToString() = 0;
	virtual bool Equals (const Object& rhs) const = 0;
};

/*
 * see: https://en.wikipedia.org/wiki/Barton%E2%80%93Nackman_trick
 * and: https://en.wikipedia.org/wiki/Curiously_recurring_template_pattern
 */
template <class T, class B>
class CRTP : public B {
public:
	  friend bool operator==(const T& a, const T& b) { return a.Equals(b); }
	  friend bool operator!=(const T& a, const T& b) { return !a.Equals(b); }
	  bool operator==(const T& b) { return this->Equals(b); }
	  bool operator!=(const T& b) { return !this->Equals(b); }
};

template <class T>
static bool EqualsHelper(const T& lhs, const Object& rhs, std::function<bool(const T&, const T&)> cmp) {
	auto right = dynamic_cast<const T*>(&rhs);
	return right == nullptr ? false : cmp(lhs, *right);
}

#endif












