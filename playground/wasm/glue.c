/* The page's entry points into the translator (`Web.lean`): C strings in, malloc'd C strings out. */
#include <lean/lean.h>
#include <stdlib.h>
#include <string.h>
#include <emscripten.h>

lean_object* initialize_playground_Web(uint8_t builtin);
lean_object* ariadne_playground_translate(lean_object* text, lean_object* namespace_, lean_object* path);
lean_object* ariadne_playground_run(lean_object* text, lean_object* call);
void lean_initialize_runtime_module(void);
void lean_io_mark_end_initialization(void);

/* The modules the translator uses from the `Lean` package (`Lean.Data.Json`) make the emitted
   initializers call `lean_initialize`, which natively also sets up the elaborator's C++ side. The
   translator never elaborates, so initializing the runtime is enough: each module's initializer
   still initializes everything it imports. */
void lean_initialize(void) { lean_initialize_runtime_module(); }

static char* take(lean_object* s) {
  size_t n = lean_string_size(s);
  char* out = malloc(n);
  memcpy(out, lean_string_cstr(s), n);
  lean_dec_ref(s);
  return out;
}

EMSCRIPTEN_KEEPALIVE int ariadne_init(void) {
  lean_initialize_runtime_module();
  lean_object* res = initialize_playground_Web(1);
  int ok = lean_io_result_is_ok(res);
  lean_dec_ref(res);
  lean_io_mark_end_initialization();
  return ok;
}

EMSCRIPTEN_KEEPALIVE char* ariadne_translate(const char* text, const char* namespace_, const char* path) {
  return take(ariadne_playground_translate(lean_mk_string(text), lean_mk_string(namespace_), lean_mk_string(path)));
}

EMSCRIPTEN_KEEPALIVE char* ariadne_run(const char* text, const char* call) {
  return take(ariadne_playground_run(lean_mk_string(text), lean_mk_string(call)));
}
