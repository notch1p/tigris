@[extern "lean_string_repeat", expose] private def leanStringRepeat (c : @&Char) (n : @&Nat) : String :=
  go c "" n where
  go c acc
  | 0 => acc
  | n + 1 => go c (acc.push c) n

/--
  performs better (w/ `memset`) if `c` is valid ascii char.
  Otherwise it is converted to a 4-bytes sequence in the ffi and requires linear time.
  `n` is `size_t` in runtime.
-/
@[always_inline, inline] def Char.repeat (c : Char) (n : Nat) : String :=
  leanStringRepeat c n

@[extern "lean_disable_stdout_buffer", expose] opaque setStdoutBuf : Bool -> IO Unit

@[extern "lean_sigint_pipe"]
opaque installSigintPipe : IO Int32
@[extern "lean_read_fd_byte"]
opaque readFdByte : @&Int32 -> IO Int32
