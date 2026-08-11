#include <errno.h>
#include <lean/lean.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#if defined(_WIN32)
#include <windows.h>
#else
#include <unistd.h>
#endif

typedef lean_obj_res OBJRES;
typedef lean_obj_arg OWNED_ARG;
typedef b_lean_obj_arg BORROWED_ARG;

enum BYTELEN { Bin = 2, Tri, Quad, Invalid = 0 };

OBJRES
string_repeat_ascii(uint8_t c, size_t n) {
  char* str = (char*)calloc(n + 1, sizeof(uint8_t));
  memset(str, c, n * sizeof(uint8_t));

  return lean_mk_string(str);
}

OBJRES lean_mk_symlink(BORROWED_ARG p1, BORROWED_ARG p2) {
  lean_string_object* ps1 = lean_to_string(p1);
  lean_string_object* ps2 = lean_to_string(p2);
#if defined(_WIN32)
  // Try as a file symlink first; retry as directory if that fails.
  if (CreateSymbolicLinkA(ps2->m_data, ps1->m_data, 0))
    return lean_io_result_mk_ok(lean_box(0));
  DWORD err = GetLastError();
  if (err == ERROR_INVALID_PARAMETER) {
    if (CreateSymbolicLinkA(ps2->m_data, ps1->m_data,
                            SYMBOLIC_LINK_FLAG_DIRECTORY))
      return lean_io_result_mk_ok(lean_box(0));
    err = GetLastError();
  }
  char msg[256];
  FormatMessageA(FORMAT_MESSAGE_FROM_SYSTEM | FORMAT_MESSAGE_IGNORE_INSERTS,
                 NULL, err, 0, msg, sizeof(msg), NULL);
  switch (err) {
    case ERROR_FILE_EXISTS:
    case ERROR_ALREADY_EXISTS:
      return lean_io_result_mk_error(
          lean_mk_io_error_already_exists(err, lean_mk_string(msg)));
    case ERROR_FILE_NOT_FOUND:
    case ERROR_PATH_NOT_FOUND:
      return lean_io_result_mk_error(
          lean_mk_io_error_no_such_thing(err, lean_mk_string(msg)));
    case ERROR_ACCESS_DENIED:
    case ERROR_PRIVILEGE_NOT_HELD:
      return lean_io_result_mk_error(
          lean_mk_io_error_permission_denied(err, lean_mk_string(msg)));
    case ERROR_DISK_FULL:
      return lean_io_result_mk_error(
          lean_mk_io_error_resource_exhausted(err, lean_mk_string(msg)));
    case ERROR_INVALID_PARAMETER:
    case ERROR_INVALID_NAME:
    case ERROR_BAD_PATHNAME:
      return lean_io_result_mk_error(
          lean_mk_io_error_invalid_argument(err, lean_mk_string(msg)));
    case ERROR_INVALID_FUNCTION:
    case ERROR_NOT_SUPPORTED:
      return lean_io_result_mk_error(
          lean_mk_io_error_unsupported_operation(err, lean_mk_string(msg)));
    default:
      return lean_io_result_mk_error(
          lean_mk_io_error_other_error(err, lean_mk_string(msg)));
  }
#else
  if (symlink(ps1->m_data, ps2->m_data) == 0)
    return lean_io_result_mk_ok(lean_box(0));
  char* msg = strerror(errno);
  switch (errno) {
    case EACCES:
      return lean_io_result_mk_error(
          lean_mk_io_error_permission_denied(errno, lean_mk_string(msg)));
    case EEXIST:
      return lean_io_result_mk_error(
          lean_mk_io_error_already_exists(errno, lean_mk_string(msg)));
    case ENOENT:
      return lean_io_result_mk_error(
          lean_mk_io_error_no_such_thing(errno, lean_mk_string(msg)));
    case ENOTDIR:
      return lean_io_result_mk_error(
          lean_mk_io_error_inappropriate_type(errno, lean_mk_string(msg)));
    case ENOSPC:
      return lean_io_result_mk_error(
          lean_mk_io_error_resource_exhausted(errno, lean_mk_string(msg)));
    case EROFS:
      return lean_io_result_mk_error(
          lean_mk_io_error_unsupported_operation(errno, lean_mk_string(msg)));
    case ENAMETOOLONG:
    case ELOOP:
      return lean_io_result_mk_error(
          lean_mk_io_error_invalid_argument(errno, lean_mk_string(msg)));
    default:
      return lean_io_result_mk_error(
          lean_mk_io_error_other_error(errno, lean_mk_string(msg)));
  }
#endif
}

enum BYTELEN codepoint_to_bytes(uint32_t c, char* s) {
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
  char* str = (char*)calloc(lenb + 1, sizeof(uint8_t));

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
  return lean_io_result_mk_ok(lean_box(0));  // runtime Unit repr
}

#if defined(_WIN32)

// -------------------- Windows implementation --------------------
static HANDLE g_ctrlEvent = NULL;

static BOOL WINAPI ctrl_handler(DWORD dwCtrlType) {
  switch (dwCtrlType) {
    case CTRL_C_EVENT:
    case CTRL_BREAK_EVENT:
      if (g_ctrlEvent) SetEvent(g_ctrlEvent);
      return TRUE;
    default:
      return FALSE;
  }
}

LEAN_EXPORT lean_obj_res lean_sigint_pipe(void) {
  if (g_ctrlEvent) {
    return lean_io_result_mk_ok(lean_box(1));
  }
  g_ctrlEvent = CreateEventW(/*lpEventAttributes*/ NULL,
                             /*bManualReset*/ TRUE,
                             /*bInitialState*/ FALSE,
                             /*lpName*/ NULL);
  if (!g_ctrlEvent) {
    return lean_mk_io_user_error(lean_mk_string("CreateEvent failed"));
  }
  if (!SetConsoleCtrlHandler(ctrl_handler, TRUE)) {
    CloseHandle(g_ctrlEvent);
    g_ctrlEvent = NULL;
    return lean_mk_io_user_error(
        lean_mk_string("SetConsoleCtrlHandler failed"));
  }
  return lean_io_result_mk_ok(lean_box(1));
}

LEAN_EXPORT lean_obj_res lean_read_fd_byte(int32_t /*fd*/) {
  if (!g_ctrlEvent) {
    return lean_io_result_mk_ok(lean_box(0));
  }
  DWORD rc = WaitForSingleObject(g_ctrlEvent, INFINITE);
  if (rc == WAIT_OBJECT_0) {
    ResetEvent(g_ctrlEvent);
    return lean_io_result_mk_ok(lean_box(1));
  } else if (rc == WAIT_FAILED) {
    return lean_mk_io_user_error(lean_mk_string("WaitForSingleObject failed"));
  } else {
    // WAIT_ABANDONED etc: treat as error
    return lean_mk_io_user_error(lean_mk_string("Unexpected wait result"));
  }
}

#else
#include <errno.h>
#include <signal.h>
#include <unistd.h>

static int32_t sig_pipe[2] = {-1, -1};

static void sigint_handler() {
  // write is async-signal-safe
  char b = 1;
  if (sig_pipe[1] >= 0) {
    (void)!write(sig_pipe[1], &b, 1);
  }
}

LEAN_EXPORT OBJRES lean_sigint_pipe() {
  if (sig_pipe[0] != -1)
    return lean_io_result_mk_ok(lean_box(sig_pipe[0]));  // already installed
  if (pipe(sig_pipe) != 0)
    return lean_mk_io_user_error(
        lean_mk_string("sigint pipe installation failed"));
  struct sigaction sa;
  memset(&sa, 0, sizeof(sa));
  sa.sa_handler = sigint_handler;
  sigemptyset(&sa.sa_mask);
  sa.sa_flags = SA_RESTART;  // restart interrupted syscalls
  if (sigaction(SIGINT, &sa, NULL) != 0) {
    close(sig_pipe[0]);
    close(sig_pipe[1]);
    sig_pipe[0] = sig_pipe[1] = -1;
    return lean_mk_io_user_error(lean_mk_string("call to sigaction() failed"));
  }
  return lean_io_result_mk_ok(lean_box(sig_pipe[0]));
}

LEAN_EXPORT lean_obj_res lean_read_fd_byte(int32_t fd) {
  char b;
  for (;;) {
    ssize_t r = read(fd, &b, 1);
    if (r == 1) return lean_io_result_mk_ok(lean_box(1));
    if (r == 0) return lean_io_result_mk_ok(lean_box(0));  // EOF
    if (errno == EINTR) continue;                          // retry
    return lean_mk_io_user_error(lean_mk_string("read() failed"));
  }
}
#endif  // _win32
