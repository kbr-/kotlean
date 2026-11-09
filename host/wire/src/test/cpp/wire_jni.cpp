// no_python: This exposes compiled Lean test oracles through the real JNI byte helpers.
#include "kotlean_jni.hpp"

extern "C" {
lean_object* initialize_kotlean_KotleanTest_WireFixture(uint8_t);
uint8_t kotlean_test_matches_event(uint64_t, lean_object*);
uint8_t kotlean_test_matches_init(uint64_t, lean_object*);
lean_object* kotlean_test_output(uint64_t);
uint8_t kotlean_test_accepts_out(lean_object*);
lean_object* kotlean_test_echo(lean_object*);

JNIEXPORT jint JNICALL JNI_OnLoad(JavaVM*, void*) {
    return kotlean::jni::initialize(initialize_kotlean_KotleanTest_WireFixture);
}

JNIEXPORT jboolean JNICALL Java_io_kotlean_WireNative_matchesEvent(
    JNIEnv* env, jobject, jlong seed, jbyteArray bytes) {
    if (!kotlean::jni::onOwnerThread(env)) return JNI_FALSE;
    auto input = kotlean::jni::fromJava(env, bytes);
    if (!input.get()) return JNI_FALSE;
    return kotlean_test_matches_event(static_cast<uint64_t>(seed), input.release());
}

JNIEXPORT jboolean JNICALL Java_io_kotlean_WireNative_matchesInit(
    JNIEnv* env, jobject, jlong seed, jbyteArray bytes) {
    if (!kotlean::jni::onOwnerThread(env)) return JNI_FALSE;
    auto input = kotlean::jni::fromJava(env, bytes);
    if (!input.get()) return JNI_FALSE;
    return kotlean_test_matches_init(static_cast<uint64_t>(seed), input.release());
}

JNIEXPORT jbyteArray JNICALL Java_io_kotlean_WireNative_output(
    JNIEnv* env, jobject, jlong seed) {
    if (!kotlean::jni::onOwnerThread(env)) return nullptr;
    kotlean::jni::Owned output(kotlean_test_output(static_cast<uint64_t>(seed)));
    return kotlean::jni::toJava(env, output.get());
}

JNIEXPORT jboolean JNICALL Java_io_kotlean_WireNative_acceptsOut(
    JNIEnv* env, jobject, jbyteArray bytes) {
    if (!kotlean::jni::onOwnerThread(env)) return JNI_FALSE;
    auto input = kotlean::jni::fromJava(env, bytes);
    if (!input.get()) return JNI_FALSE;
    return kotlean_test_accepts_out(input.release());
}

JNIEXPORT jbyteArray JNICALL Java_io_kotlean_WireNative_echo(
    JNIEnv* env, jobject, jbyteArray bytes) {
    if (!kotlean::jni::onOwnerThread(env)) return nullptr;
    auto input = kotlean::jni::fromJava(env, bytes);
    if (!input.get()) return nullptr;
    kotlean::jni::Owned output(kotlean_test_echo(input.release()));
    return kotlean::jni::toJava(env, output.get());
}
}
