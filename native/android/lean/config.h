// no_c: Lean's Android runtime requires this C configuration header.
#pragma once
#include <lean/version.h>
#include <stdlib.h>
#define LEAN_IS_STAGE0 0
#define free_sized kotlean_free_sized
#ifdef __cplusplus
extern "C"
#endif
void kotlean_free_sized(void *ptr, size_t size);
