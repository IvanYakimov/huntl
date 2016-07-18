#ifndef __MEMORY_MAP_HPP__
#define __MEMORY_MAP_HPP__

namespace memory {
	class MemoryMapInterface;
	using MemoryMapPtr = std::shared_ptr<MemoryMapInterface>;
	using MemoryMapRef = MemoryMapInterface&;
	using RegisterName = const llvm::Value*;
	/// Display stub. This is rather a local memory than a display.
	class MemoryMapInterface{
	public:
		//NONCOPYABLE(MemoryMapInterface);
		virtual ~MemoryMapInterface() {}

		virtual HolderPtr Load(RegisterName address) = 0;
		virtual void Store(RegisterName address, HolderPtr holder) = 0;
		virtual void Print() = 0;
	};
}

#endif
