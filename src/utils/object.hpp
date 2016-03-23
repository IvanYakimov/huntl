#ifndef __OBJECT_HPP__
#define __OBJECT_HPP__

# include <memory>
# include <string>
# include <iostream>

//TODO: VERIFY!!! from_this !
/** Base class for all shared objects in the program.
 * \note inheritance from std::enable_shared_from_this<Object> allows
 * to refer to 'this' pointer from code. */
class Object : public std::enable_shared_from_this<Object> {
public:
	virtual ~Object() {}
	/** Returns true if a and b are structuraly equivalent, and false otherwise.
	 * \note Use EqualsHelper () to implement equality checking in overloaded functions.
	 * \see EqualsHelper
	 * \see operator==(const T& a, const T& b) */
	virtual bool Equals (const Object& rhs) const = 0;
	/** Returns string representation in appropriate format.
	 * Any class, inherited (transitevly) from Object by CRTP <T,B> has streaming operator<<,
	 * which invokes this  method to put the string representation into a stream.
	 * \see std::ostream& operator<<(std::ostream &os, const T& obj) */
	virtual std::string ToString() const = 0;
};

/** Static (F-bound) polymorphism idiom implementation.
 * \tparam T - type of the target class
 * \tparam B - type of the parent class
 * \see https://en.wikipedia.org/wiki/Barton%E2%80%93Nackman_trick
 * \see https://en.wikipedia.org/wiki/Curiously_recurring_template_pattern */
template <class T, class B>
class CRTP : public B {
public:
	/** Equality operator.
	 * To provide correct behavior of operator== one should overload Equals method in class T.
	 * \see Object::Equals */
	friend bool operator==(const T& a, const T& b) { return a.Equals(b); }
	  /** Distinction operator.
	   * To provide correct behavior of operator== one should overload Equals method in class T.
	   * \see Object::Equals */
	friend bool operator!=(const T& a, const T& b) { return !a.Equals(b); }
	/** \see operator==(const T& a, const T& b)  */
	bool operator==(const T& b) { return this->Equals(b); }
	/** \see operator!=(const T& a, const T& b)  */
	bool operator!=(const T& b) { return !this->Equals(b); }
	/** Streaming operator.
	 * To provide correct behavior of the operator<< one should overload ToString() method in class T. */
	friend std::ostream& operator<<(std::ostream &os, const T& obj) {
		os << obj.ToString();
		return os;
	}
};

/** Helper function for Object::Equals() overloading.
 * \note To use it one should provide comparison function cmp, which accepts two T-type objects and compares their fields.
 * The code of comparison function may looks like this:
 * \code
 * auto cmp = [] (auto lhs, auto rhs) -> bool {
 * 		return lhs.field1 == rhs.field1
 * 			and lhs.field2 == rhs.field2
 * 			and ...
 * 			and lns.fieldn == rhs.fieldn;
 * };
 * \endcode
 * \see Object::Equals() */
template <class T>
/*static*/ inline bool EqualsHelper(const T& lhs, const Object& rhs, std::function<bool(const T&, const T&)> cmp) {
	//TODO: check correctness of this method
	auto right = dynamic_cast<const T*>(&rhs);
	return right == nullptr ? false : cmp(lhs, *right);
}

/** Check whether its param is instance of T.
 * It is something like Java instanceof keyword.
 * \note In most cases it should be applied only for instances of (smart pointers to) classes,
 * derived (transitively) from Object
 * \attention it works only for std::shared_pointer-s!
 * \see Object
 */
template<class T, class U>
bool instanceof( const std::shared_ptr<U>& r ) noexcept {
    if (std::dynamic_pointer_cast<T>(r) != nullptr)
    	return true;
    else
        return false;
}

#endif












