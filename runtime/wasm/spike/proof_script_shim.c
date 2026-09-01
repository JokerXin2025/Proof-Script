#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include <lean/lean.h>

#ifdef __cplusplus
extern "C" {
#endif

/* Declared by Lean's Emscripten runtime, but not part of lean.h. */
extern void lean_initialize_runtime_module(void);
extern lean_obj_res proof_script_spike(lean_obj_arg input);
extern lean_obj_res initialize_runtime_wasm_spike_Spike(uint8_t builtin);

void proof_script_init(void) {
  lean_initialize_runtime_module();
  lean_object *result = initialize_runtime_wasm_spike_Spike(0);
  lean_dec(result);
}

uint32_t proof_script_alloc(uint32_t size) {
  return (uint32_t)(uintptr_t)malloc(size);
}

void proof_script_free(uint32_t ptr) {
  free((void *)(uintptr_t)ptr);
}

uint32_t proof_script_invoke(uint32_t input_ptr, uint32_t input_len,
                            uint32_t output_ptr, uint32_t output_capacity) {
  (void)output_ptr;
  if (input_len > 0 && input_ptr == 0) return 0;

  lean_object *input = lean_mk_string_from_bytes((char const *)(uintptr_t)input_ptr,
                                                  input_len);
  lean_object *result = proof_script_spike(input);
  char const *text = lean_string_cstr(result);
  uint32_t length = (uint32_t)strlen(text);
  if (length > output_capacity) {
    lean_dec(result);
    return length;
  }
  memcpy((void *)(uintptr_t)output_ptr, text, length);
  lean_dec(result);
  return length;
}

#ifdef __cplusplus
}
#endif
