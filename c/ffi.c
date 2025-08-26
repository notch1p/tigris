#include <lean/lean.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef lean_obj_res OBJRES;
typedef lean_obj_arg OWNED_ARG;
typedef b_lean_obj_arg BORROWED_ARG;

enum BYTELEN { Bin = 2, Tri, Quad, Invalid = 0 };

OBJRES
string_repeat_ascii(uint8_t c, size_t n) {
  char *str = (char *)calloc(n + 1, sizeof(uint8_t));
  memset(str, c, n * sizeof(uint8_t));

  return lean_mk_string(str);
}

enum BYTELEN codepoint_to_bytes(uint32_t c, char *s) {
  if (c < 0x800) {
    s[0] = 0xC0 | c >> 6;
    s[1] = 0x80 | c & 0x3F;
    return Bin;
  } else if (c < 0x10000) {
    s[0] = 0xE0 | c >> 12;
    s[1] = 0x80 | (c >> 6) & 0x3F;
    s[2] = 0x80 | c & 0x3F;
    return Tri;
  } else if (c < 0x10FFFF) {
    s[0] = 0xF0 | c >> 18;
    s[1] = 0x80 | (c >> 12) & 0x3F;
    s[2] = 0x80 | (c >> 6) & 0x3F;
    s[3] = 0x80 | c & 0x3F;
    return Quad;
  }
  return Invalid;
}

OBJRES
string_repeat_utf8(uint32_t c, size_t n) {
  char bytes[4];
  size_t len = codepoint_to_bytes(c, bytes);
  assert(len);

  size_t lenb = n * len;
  char *str = (char *)calloc(lenb + 1, sizeof(uint8_t));

  for (size_t i = 0; i < n; i++) {
    memcpy(str + i * len, bytes, len);
  };

  return lean_mk_string(str);
}

LEAN_EXPORT OBJRES lean_string_repeat(uint32_t c, BORROWED_ARG /* Nat */ n) {
  size_t len = lean_usize_of_nat(n);
  return c < 0x80 ? string_repeat_ascii(c, len) : string_repeat_utf8(c, len);
}

LEAN_EXPORT OBJRES lean_disable_stdout_buffer(uint8_t i) {
  if (i == 0) {
    setbuf(stdout, NULL);
  }
  return lean_io_result_mk_ok(lean_box(0)); // runtime Unit repr
}
