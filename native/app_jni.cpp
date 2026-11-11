// no_cpp: JNI requires native object ownership and Java field and byte-array access.
#include "kotlean_jni.hpp"

#ifndef KOTLEAN_INITIALIZER
#error "Define KOTLEAN_INITIALIZER as the app module's generated runtime initializer"
#endif

extern "C" {
lean_object* KOTLEAN_INITIALIZER(uint8_t);
lean_object* kotlean_init(lean_object*);
lean_object* kotlean_step(lean_object*, lean_object*);
lean_object* kotlean_free(lean_object*);
}

namespace {
using kotlean::jni::Owned;

jfieldID handleField(JNIEnv* env, jobject session) {
    jclass type = env->GetObjectClass(session);
    if (!type) return nullptr;
    jfieldID field = env->GetFieldID(type, "handle", "J");
    env->DeleteLocalRef(type);
    return field;
}

lean_object* stateAt(JNIEnv* env, jobject session, jfieldID field) {
    const jlong handle = env->GetLongField(session, field);
    return handle ? reinterpret_cast<lean_object*>(static_cast<uintptr_t>(handle)) : lean_box(0);
}

jbyteArray publish(JNIEnv* env, jobject session, jfieldID field, b_lean_obj_arg packet) {
    jbyteArray bytes = kotlean::jni::toJava(env, lean_ctor_get(packet, 1));
    if (!bytes) return nullptr;
    lean_object* state = lean_ctor_get(packet, 0);
    lean_inc(state);
    lean_object* previous = stateAt(env, session, field);
    env->SetLongField(session, field, static_cast<jlong>(reinterpret_cast<uintptr_t>(state)));
    Owned released(kotlean_free(previous));
    return bytes;
}
}

extern "C" {
JNIEXPORT jint JNICALL JNI_OnLoad(JavaVM*, void*) {
    return kotlean::jni::initialize(KOTLEAN_INITIALIZER);
}

JNIEXPORT jbyteArray JNICALL Java_io_kotlean_NativeSession_start(
    JNIEnv* env, jobject session, jbyteArray bytes) {
    if (!kotlean::jni::onOwnerThread(env)) return nullptr;
    jfieldID field = handleField(env, session);
    if (!field) return nullptr;
    auto input = kotlean::jni::fromJava(env, bytes);
    if (!input.get()) return nullptr;
    Owned packet(kotlean_init(input.release()));
    return publish(env, session, field, packet.get());
}

JNIEXPORT jbyteArray JNICALL Java_io_kotlean_NativeSession_step(
    JNIEnv* env, jobject session, jbyteArray bytes) {
    if (!kotlean::jni::onOwnerThread(env)) return nullptr;
    jfieldID field = handleField(env, session);
    if (!field) return nullptr;
    auto input = kotlean::jni::fromJava(env, bytes);
    if (!input.get()) return nullptr;
    lean_object* state = stateAt(env, session, field);
    lean_inc(state);
    Owned packet(kotlean_step(state, input.release()));
    return publish(env, session, field, packet.get());
}

JNIEXPORT void JNICALL Java_io_kotlean_NativeSession_close(JNIEnv* env, jobject session) {
    if (!kotlean::jni::onOwnerThread(env)) return;
    jfieldID field = handleField(env, session);
    if (!field) return;
    lean_object* state = stateAt(env, session, field);
    env->SetLongField(session, field, 0);
    Owned released(kotlean_free(state));
}
}
