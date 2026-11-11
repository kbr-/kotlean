// no_cpp: JNI requires C++ ownership and byte-array access.
#pragma once

#include <jni.h>
#include <lean/lean.h>
#include <stdint.h>
#include <pthread.h>

namespace kotlean::jni {

// fromJava creates one owned Lean reference. release transfers it to an owned exported argument,
// which Lean consumes. A returned object is owned by its receiving Owned instance; toJava borrows
// it while copying, then Owned releases it. Failure before transfer also releases the reference
// through Owned.

class Owned {
    lean_object* object_;
public:
    explicit Owned(lean_object* object) : object_(object) {}
    Owned(const Owned&) = delete;
    Owned& operator=(const Owned&) = delete;
    Owned(Owned&& other) noexcept : object_(other.release()) {}
    ~Owned() { if (object_) lean_dec(object_); }
    lean_object* get() const { return object_; }
    lean_object* release() { auto* result = object_; object_ = nullptr; return result; }
};

inline pthread_t owner;

inline void raise(JNIEnv* env, const char* type, const char* message) {
    jclass exception = env->FindClass(type);
    if (exception) {
        env->ThrowNew(exception, message);
        env->DeleteLocalRef(exception);
    }
}

inline bool onOwnerThread(JNIEnv* env) {
    if (pthread_equal(pthread_self(), owner)) return true;
    raise(env, "java/lang/IllegalStateException", "Kotlean must run on its initializing thread");
    return false;
}

inline jint initialize(lean_object* (*module)(uint8_t)) {
    Owned result(module(1));
    if (lean_io_result_is_error(result.get())) {
        lean_io_result_show_error(result.get());
        return JNI_ERR;
    }
    lean_io_mark_end_initialization();
    owner = pthread_self();
    return JNI_VERSION_1_6;
}

inline Owned fromJava(JNIEnv* env, jbyteArray bytes) {
    if (!bytes) {
        raise(env, "java/lang/NullPointerException", "Kotlean byte array is null");
        return Owned(nullptr);
    }
    const jsize size = env->GetArrayLength(bytes);
    if (env->ExceptionCheck()) return Owned(nullptr);
    Owned result(lean_alloc_sarray(1, static_cast<size_t>(size), static_cast<size_t>(size)));
    env->GetByteArrayRegion(bytes, 0, size, reinterpret_cast<jbyte*>(lean_sarray_cptr(result.get())));
    if (env->ExceptionCheck()) return Owned(nullptr);
    return result;
}

inline jbyteArray toJava(JNIEnv* env, b_lean_obj_arg bytes) {
    const size_t size = lean_sarray_size(bytes);
    static_assert(sizeof(jsize) == sizeof(int32_t));
    if (size > static_cast<size_t>(INT32_MAX)) {
        raise(env, "java/lang/OutOfMemoryError", "Kotlean output exceeds the JVM array limit");
        return nullptr;
    }
    jbyteArray result = env->NewByteArray(static_cast<jsize>(size));
    if (!result) return nullptr;
    env->SetByteArrayRegion(result, 0, static_cast<jsize>(size),
        reinterpret_cast<const jbyte*>(lean_sarray_cptr(bytes)));
    if (env->ExceptionCheck()) return nullptr;
    return result;
}

}
