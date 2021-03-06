#ifndef __OBJECT_HPP__
#define __OBJECT_HPP__

//#define __STDC_LIMIT_MACROS
//#define __STDC_CONSTANT_MACROS

# include <memory>
# include <string>
# include <iostream>
# include <sstream>

// Original Version
#define NONCOPYABLE(T) \
T(const T&) = delete; \
void operator=(const T&) = delete;

#define COMPARABLE(T) \
friend bool operator==(const T& a, const T& b) { return a.Equals(b); } \
friend bool operator!=(const T& a, const T& b) { return !a.Equals(b); } \
bool operator==(const T& b) { return this->Equals(b); } \
bool operator!=(const T& b) { return !this->Equals(b); } \

#define PRINTABLE(T) \
friend std::ostream& operator<<(std::ostream &os, const T& obj) { \
	return obj.ToStream(os, obj); \
} \

//TODO: VERIFY!!! from_this !
/** Base class for all shared objects in the program.
 * \note inheritance from std::enable_shared_from_this<Object> allows
 * to refer to 'this' pointer from code. */
class Object : public std::enable_shared_from_this<Object> {
public:
	virtual ~Object() {}
	virtual bool Equals (const Object& rhs) const = 0;
	virtual std::ostream& ToStream(std::ostream &os, const Object& obj) const = 0;
	template <class T, class B>
	inline static std::shared_ptr<T> UpCast(std::shared_ptr<B> arg) {
		auto res = std::dynamic_pointer_cast<T>(arg);
		assert (res != nullptr);
		return res;
	}
};

/**
 * TODO: documentation
 */
using ObjectPtr = std::shared_ptr<Object>;

/** Static (F-bound) polymorphism idiom implementation.
 * \tparam T - type of the target class
 * \tparam B - type of the parent class
 * \see https://en.wikipedia.org/wiki/Barton%E2%80%93Nackman_trick
 * \see https://en.wikipedia.org/wiki/Curiously_recurring_template_pattern */
template <class T, class B>
class shared : public B {
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
 * \tparam T - type of compared objects
 * \param lhs - this (left) object
 * \param rhs - target (right) object, should be (smart pointer to) an instance of T
 * \param cmp - comparison operator, should return true if lhs and rhs are structurally equivalent and false otherwise.
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
	//TODO: replace dynamic by static cast
	auto right = dynamic_cast<const T*>(&rhs);
	return right == nullptr ? false : cmp(lhs, *right);
}


#endif /*__OBJECT_HPP__*/

