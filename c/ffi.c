#include <errno.h>
#include <fcntl.h>
#include <lean/lean.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <termios.h>
#include <unistd.h>

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
static int32_t sig_pipe[2] = {-1, -1};

static void sigint_handler() {
  // write is async-signal-safe
  char b = 1;
  if (sig_pipe[1] >= 0) {
    write(sig_pipe[1], &b, 1);
  }
}

LEAN_EXPORT OBJRES lean_sigint_pipe() {
#if defined(__unix__) || defined(__APPLE__)
  if (sig_pipe[0] != -1)
    return lean_io_result_mk_ok(lean_box(sig_pipe[0])); // already installed
  if (pipe(sig_pipe) != 0)
    return lean_mk_io_user_error(
        lean_mk_string("sigint pipe installation failed"));
  struct sigaction sa;
  memset(&sa, 0, sizeof(sa));
  sa.sa_handler = sigint_handler;
  sigemptyset(&sa.sa_mask);
  sa.sa_flags = SA_RESTART; // restart interrupted syscalls
  if (sigaction(SIGINT, &sa, NULL) != 0) {
    close(sig_pipe[0]);
    close(sig_pipe[1]);
    sig_pipe[0] = sig_pipe[1] = -1;
    return lean_mk_io_user_error(lean_mk_string("call to sigaction() failed"));
  }
  return lean_io_result_mk_ok(lean_box(sig_pipe[0]));
#else
  return lean_io_result_mk_ok(lean_box(-1));
#endif
}

LEAN_EXPORT OBJRES lean_read_fd_byte(int32_t fd) {
#if defined(__unix__) || defined(__APPLE__)
  char b;
  for (;;) {
    ssize_t r = read(fd, &b, 1);
    if (r == 1)
      return lean_io_result_mk_ok(lean_box(1));
    if (r == 0)
      return lean_io_result_mk_ok(lean_box(0)); // EOF
    if (errno == EINTR)
      continue; // retry
    return lean_mk_io_user_error(
        lean_mk_string("call to read() failed")); // other error
  }
#else
  return lean_io_result_mk_ok(lean_box(0));
#endif
}

LEAN_EXPORT OBJRES lean_read_stdin_line() {
#if defined(__unix__) || defined(__APPLE__)
  size_t cap = 256;
  size_t len = 0;
  char *buf = (char *)malloc(cap);
  if (!buf)
    return lean_mk_io_error_resource_exhausted(ENOMEM,
                                               lean_mk_string("out of memory"));

  for (;;) {
    char ch;
    ssize_t r = read(STDIN_FILENO, &ch, 1);
    if (r == 1) {
      if (len + 1 >= cap) {
        cap <<= 1;
        char *nbuf = (char *)realloc(buf, cap);
        if (!nbuf) {
          free(buf);
          return lean_mk_io_error_resource_exhausted(
              ENOMEM, lean_mk_string("out of memory"));
        }
        buf = nbuf;
      }
      buf[len++] = ch;
      if (ch == '\n')
        break;
    } else if (r == 0) {
      /* EOF */
      if (len == 0) {
        free(buf);
        return lean_io_result_mk_ok(lean_mk_string(""));
      } else {
        break;
      }
    } else {
      if (errno == EIO || errno == EINTR) {
        /* macOS can return EIO on TTY after SIGINT; treat like EINTR and retry
         */
        continue;
      }
      free(buf);
      return lean_mk_io_error_hardware_fault(
          EIO, lean_mk_string("read(stdin) error"));
    }
  }

  buf[len] = 0;
  lean_obj_res s = lean_mk_string(buf);
  free(buf);
  return lean_io_result_mk_ok(s);
#else
  char *line = NULL;
  size_t n = 0;
  ssize_t r = getline(&line, &n, stdin);
  if (r < 0) {
    if (line)
      free(line);
    return lean_io_result_mk_ok(lean_mk_string(""));
  }
  lean_obj_res s = lean_mk_string(line);
  free(line);
  return lean_io_result_mk_ok(s);
#endif
}

LEAN_EXPORT OBJRES lean_clear_stdin_error() {
#if defined(__unix__) || defined(__APPLE__)
  clearerr(stdin);
  tcflush(STDIN_FILENO, TCIFLUSH);
#endif
  return lean_io_result_mk_ok(lean_box(0));
}
