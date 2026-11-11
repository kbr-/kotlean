// no_cpp: The JVM ownership control reads the real Lean allocator and retains a leaking control.
#include "kotlean_jni.hpp"
#include <lean/mimalloc.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>

namespace {
lean_object* trackedModel = nullptr;
struct Buffer { char* data; size_t size; };
void append(const char* message, void* argument) {
    auto* buffer = static_cast<Buffer*>(argument);
    const size_t size = strlen(message);
    auto* data = static_cast<char*>(realloc(buffer->data, buffer->size + size + 1));
    if (!data) abort();
    memcpy(data + buffer->size, message, size + 1);
    buffer->data = data;
    buffer->size += size;
}
}

extern "C" {
JNIEXPORT void JNICALL Java_io_kotlean_AppAllocator_trackModel(JNIEnv* env, jobject, jobject session) {
    if (!kotlean::jni::onOwnerThread(env)) return;
    jclass type = env->GetObjectClass(session);
    if (!type) return;
    jfieldID field = env->GetFieldID(type, "handle", "J");
    env->DeleteLocalRef(type);
    if (!field) return;
    auto* option = reinterpret_cast<lean_object*>(static_cast<uintptr_t>(env->GetLongField(session, field)));
    trackedModel = lean_ctor_get(lean_ctor_get(option, 0), 0);
    lean_inc(trackedModel);
}

JNIEXPORT jint JNICALL Java_io_kotlean_AppAllocator_releaseModel(JNIEnv* env, jobject) {
    if (!kotlean::jni::onOwnerThread(env)) return -1;
    const jint count = lean_internal_get_rc(trackedModel);
    lean_dec(trackedModel);
    trackedModel = nullptr;
    return count;
}

JNIEXPORT jstring JNICALL Java_io_kotlean_AppAllocator_references(JNIEnv* env, jobject, jobject session) {
    if (!kotlean::jni::onOwnerThread(env)) return nullptr;
    jclass type = env->GetObjectClass(session);
    if (!type) return nullptr;
    jfieldID field = env->GetFieldID(type, "handle", "J");
    env->DeleteLocalRef(type);
    if (!field) return nullptr;
    const jlong handle = env->GetLongField(session, field);
    if (!handle) return env->NewStringUTF("closed");
    auto* option = reinterpret_cast<lean_object*>(static_cast<uintptr_t>(handle));
    if (lean_is_scalar(option)) return env->NewStringUTF("absent");
    auto* state = lean_ctor_get(option, 0);
    auto* model = lean_ctor_get(state, 0);
    char message[128];
    snprintf(message, sizeof(message), "option=%d state=%d model=%d", lean_internal_get_rc(option),
        lean_internal_get_rc(state), lean_is_scalar(model) ? 0 : lean_internal_get_rc(model));
    return env->NewStringUTF(message);
}

JNIEXPORT jstring JNICALL Java_io_kotlean_AppAllocator_stats(JNIEnv* env, jobject) {
    if (!kotlean::jni::onOwnerThread(env)) return nullptr;
    Buffer buffer{nullptr, 0};
    mi_stats_print_out(append, &buffer);
    jstring result = env->NewStringUTF(buffer.data ? buffer.data : "");
    free(buffer.data);
    return result;
}

JNIEXPORT void JNICALL Java_io_kotlean_AppAllocator_retain(JNIEnv* env, jobject, jobject session) {
    if (!kotlean::jni::onOwnerThread(env)) return;
    jclass type = env->GetObjectClass(session);
    if (!type) return;
    jfieldID field = env->GetFieldID(type, "handle", "J");
    env->DeleteLocalRef(type);
    if (!field) return;
    const jlong handle = env->GetLongField(session, field);
    if (handle) lean_inc(reinterpret_cast<lean_object*>(static_cast<uintptr_t>(handle)));
}
}
