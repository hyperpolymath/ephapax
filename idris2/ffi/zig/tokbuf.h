#ifndef EPHAPAX_TOKBUF_H
#define EPHAPAX_TOKBUF_H

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

void *eph_tokbuf_new(int32_t cap);
void eph_tokbuf_free(void *buf);
void eph_tokbuf_push(void *buf, int32_t tag, const char *str_ptr, int32_t str_len, int32_t bool_val, int32_t line, int32_t col);
int32_t eph_tokbuf_len(void *buf);
int32_t eph_tokbuf_kind(void *buf, int32_t idx);
char *eph_tokbuf_str_ptr(void *buf, int32_t idx);
int32_t eph_tokbuf_str_len(void *buf, int32_t idx);
int32_t eph_tokbuf_bool(void *buf, int32_t idx);
int32_t eph_tokbuf_line(void *buf, int32_t idx);
int32_t eph_tokbuf_col(void *buf, int32_t idx);

#ifdef __cplusplus
}
#endif

#endif
