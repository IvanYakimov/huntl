# ifndef __MEMORY_HPP__
# define __MEMORY_HPP__

template<typename T, typename... Args>
std::unique_ptr<T> make_unique(Args&&... args) {
    return std::unique_ptr<T>(new T(std::forward<Args>(args)...));
}

# endif /* __MEMORY_HPP__ */
