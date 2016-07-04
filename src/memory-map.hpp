#ifndef __MEMORY_MAP_HPP__
#define __MEMORY_MAP_HPP__

namespace memory {
	class MemoryMapInterface;
	using MemoryMapPtr = std::shared_ptr<MemoryMapInterface>;
	/// Display stub. This is rather a local memory than a display.
	class MemoryMapInterface{
	public:
		NONCOPYABLE(MemoryMapInterface);
		virtual ~MemoryMapInterface() {}
		using Address = const llvm::Value*;
		virtual HolderPtr Load(Address address) = 0;
		virtual void Store(Address address, HolderPtr holder) = 0;
	};
}

#endif
