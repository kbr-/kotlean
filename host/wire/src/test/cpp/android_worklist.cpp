// no_cpp: This control needs native pointer words and the runtime's private C++ worklist.
#include KOTLEAN_RUNTIME_OBJECT
#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <random>
#include <vector>

// Allocator addresses are the oracle: every popped pointer must retain every bit and LIFO order.
int main() {
    constexpr std::size_t capacity = 128;
    std::vector<lean_object*> allocated;
    for (std::size_t index = 0; index < capacity; ++index) {
        auto* value = static_cast<lean_object*>(std::malloc(sizeof(lean_object)));
        if (!value) return 3;
        std::memset(value, 0, sizeof(lean_object));
        if ((reinterpret_cast<std::uintptr_t>(value) >> 56) == 0) {
            std::puts("Control unavailable: Android allocator returned an untagged pointer");
            return 3;
        }
        allocated.push_back(value);
    }
    std::mt19937_64 random(715091);
    for (unsigned trial = 0; trial < 4; ++trial) {
        std::shuffle(allocated.begin(), allocated.end(), random);
        for (std::size_t count = 0; count <= capacity; ++count) {
#ifdef KOTLEAN_ORIGINAL_WORKLIST
            lean_object* todo = nullptr;
#else
            lean::deletion_worklist todo;
#endif
            for (std::size_t index = 0; index < count; ++index) {
                std::memset(allocated[index], 0, sizeof(lean_object));
                lean::push_back(todo, allocated[index]);
            }
            for (std::size_t index = count; index > 0; --index) {
                auto* actual = lean::pop_back(todo);
                auto* expected = allocated[index - 1];
                if (reinterpret_cast<std::uintptr_t>(actual) !=
                    reinterpret_cast<std::uintptr_t>(expected)) {
                    std::printf("Pointer-word mismatch: depth=%zu trial=%u\n", count, trial);
                    return 1;
                }
            }
#ifdef KOTLEAN_ORIGINAL_WORKLIST
            if (todo != nullptr) return 2;
#else
            if (!todo.empty()) return 2;
#endif
        }
    }
    for (auto* value : allocated) std::free(value);
    std::puts("Full-pointer worklist: allocator pointer words and LIFO order preserved through depth 128");
    return 0;
}
