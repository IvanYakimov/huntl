#ifndef __OBJECT_HPP__
#define __OBJECT_HPP__

# include <memory>
# include <string>
# include <iostream>

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
	os << obj.ToString(); \
	return os; \
}

//TODO: VERIFY!!! from_this !
//TODO: ALL shared objects MUST be IMMUTABLE!
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

/** Every immutable shared object must be inherited from this.
 */
class Immutable : public Object {
public:
	virtual ~Immutable() {}
};

/** Evey mutalbe shared object must be inherited from this.
 */
class Mutable : public Object {
public:
	virtual ~Mutable() {}
	virtual ObjectPtr Clone() = 0;
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
	auto right = dynamic_cast<const T*>(&rhs);
	return right == nullptr ? false : cmp(lhs, *right);
}

/** Check whether its param is instance of T.
 * It is something like Java instanceof keyword.
 * \note In most cases it should be applied only for instances of (smart pointers to) classes,
 * derived (transitively) from Object
 * \param obj - target object
 * \tparam T - target type
 * \tparam U - type of obj (can be skipped)
 * \attention it works only for std::shared_pointer-s!
 * \see Object
 */
template<class T, class U>
bool instanceof( const std::shared_ptr<U>& obj ) noexcept {
    if (std::dynamic_pointer_cast<T>(obj) != nullptr)
    	return true;
    else
        return false;
}

/** Allocates new unique-pointed object.
 * \tparam T - type of the allocated object
 * \tparam Args - list of arguments, which should be passed to a constructor of the allocated object
 */
template<typename T, typename... Args>
std::unique_ptr<T> make_unique(Args&&... args) {
    return std::unique_ptr<T>(new T(std::forward<Args>(args)...));
}


/** TODO: documentation
 */
template <typename X, typename A, typename... Args>
inline void Assert(A assertion, Args&&... args) {
	if (not assertion)
		throw X(std::forward<Args>(args)...);
}

/**
 * deprecated
 */
#define CONTRACT
template <typename INIT, typename MORE_INIT, typename INV_IN, typename PRE, typename FUNC, typename POST, typename INV_OUT>
inline void Contract(INIT init, MORE_INIT more_init, INV_IN inv_in, PRE pre, FUNC func, POST post, INV_OUT inv_out) {
	init();
#ifdef CONTRACT
	more_init();
	auto x = inv_in();
	pre();
#endif
	func();
#ifdef CONTRACT
	post();
	inv_out(x);
#endif
}

#ifdef CONTRACT
#define PRE
#define POST
#endif /*CONTRACT*/

#endif /*__OBJECT_HPP__*/












