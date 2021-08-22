#include <stdio.h>
#include <inttypes.h>
#include <stdlib.h>
#include "types.h"
#include "runtime.h"

FILE* in;
FILE* out;
void (*error_handler)();
int64_t *heap;

void print_result(int64_t);

void error_exit() {
  printf("err\n");
  exit(1);
}

void raise_error() {
  return error_handler();
}

int main(int argc, char** argv) {
  in = stdin;
  out = stdout;
  error_handler = &error_exit;
  heap = malloc(8 * heap_size);
  int64_t result = entry(heap);
  // See if we need to print the initial tick
  if (cons_type_tag == (ptr_type_mask & result)) printf("'");
  print_result(result);
  if (result != val_void) printf("\n");
  free(heap);
  return 0;
}

void print_char(int64_t);
void print_cons(int64_t);
void print_closure(int64_t);

void print_result(int64_t result) {
  if (cons_type_tag == (ptr_type_mask & result)) {
    printf("(");
    print_cons(result);
    printf(")");
  } else if (box_type_tag == (ptr_type_mask & result)) {
    printf("#&");
    print_result (*((int64_t *)(result ^ box_type_tag)));
  } else if (proc_type_tag == (ptr_type_mask & result)) {
    printf("<procedure>\n");
    print_closure(result);
  } else if (int_type_tag == (int_type_mask & result)) {
    printf("%" PRId64, result >> int_shift);
  } else if (char_type_tag == (char_type_mask & result)) {
    print_char(result);
  } else {
    switch (result) {
    case val_true:
      printf("#t"); break;
    case val_false:
      printf("#f"); break;
    case val_eof:
      printf("#<eof>"); break;
    case val_empty:
      printf("()"); break;
    case val_void:
      /* nothing */ break;
    }
  }  
}

void print_closure(int64_t proc) {
 int64_t num_expected_args = *((int64_t *)((proc + 8) ^ proc_type_tag));
 int64_t num_predef_args   = *((int64_t *)((proc + 16) ^ proc_type_tag)); 
 int64_t num_free_vars     = *((int64_t *)((proc + 24) ^ proc_type_tag));
 printf("Expected args: %ld \n", num_expected_args);
 
 printf("# of Predef args: %ld\t{", num_predef_args);

 int i = 0; 
 for(i = 0; (long)i < num_predef_args; i++) {
   int64_t val = *((int64_t *)((proc + 32 + 8*i +(num_free_vars*((long)8))) ^ proc_type_tag)); 
   print_result(val); 
   printf(" "); 
 }
 printf("}\n");

 printf("# of Free Vars: %ld", num_free_vars);
}

void print_cons(int64_t a) {  
  int64_t car = *((int64_t *)((a + 8) ^ cons_type_tag));
  int64_t cdr = *((int64_t *)((a + 0) ^ cons_type_tag));
  print_result(car);
  if (cdr == val_empty) {
    // nothing
  } else if (cons_type_tag == (ptr_type_mask & cdr)) {
    printf(" ");
    print_cons(cdr);
  } else {
    printf(" . ");
    print_result(cdr);
  }
}
