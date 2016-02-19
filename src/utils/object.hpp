#ifndef __OBJECT_HPP__
#define __OBJECT_HPP__

# include <memory>
# include <string>
# include <iostream>

//TODO: make object.o file
class Object : public std::enable_shared_from_this<Object> {
public:
	virtual ~Object() {}
	virtual bool Equals (const Object& rhs) const = 0;
	virtual std::string ToString() const = 0;
};

/*
 * see: https://en.wikipedia.org/wiki/Barton%E2%80%93Nackman_trick
 * and: https://en.wikipedia.org/wiki/Curiously_recurring_template_pattern
 */
/*
 * T = type of the class
 * B = type of the parent class
 */
template <class T, class B>
class CRTP : public B {
public:
	  friend bool operator==(const T& a, const T& b) { return a.Equals(b); }
	  friend bool operator!=(const T& a, const T& b) { return !a.Equals(b); }
	  bool operator==(const T& b) { return this->Equals(b); }
	  bool operator!=(const T& b) { return !this->Equals(b); }
	  friend std::ostream& operator<<(std::ostream &os, const T& obj) {
		  os << obj.ToString();
		  return os;
	  }
};

template <class T>
//TODO: static? - create .o file for object
static inline bool EqualsHelper(const T& lhs, const Object& rhs, std::function<bool(const T&, const T&)> cmp) {
	//TODO: check correctness of this method
	auto right = dynamic_cast<const T*>(&rhs);
	return right == nullptr ? false : cmp(lhs, *right);
}

template<class T, class U>
bool instanceof( const std::shared_ptr<U>& r ) noexcept {
    if (std::dynamic_pointer_cast<T>(r) != nullptr)
    	return true;
    else
        return false;
}

#endif












