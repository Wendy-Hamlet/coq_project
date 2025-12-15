#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"
#include "sll_shape_def.h"

unsigned int arr_sum(int n, unsigned int *a)
/*@ Require 0 <= n && n < INT_MAX && UIntArray::full_shape(a, n)
    Ensure UIntArray::full_shape(a, n) */
{
  int i;
  unsigned int ret = 0;
  /*@ Inv 
      exists v, ret == v &&
      0 <= i && i <= n@pre 
  */
  for (i = 0; i < n; ++i) {
    ret += a[i];
  }
  return ret;
}

void array_copy1(int *dest, int *src, int n)
/*@ Require 0 <= n && n < INT_MAX && IntArray::undef_full(dest, n) * IntArray::full_shape(src, n)
    Ensure IntArray::full_shape(dest, n) * IntArray::full_shape(src, n)
*/
{
  int i;
  /*@ Inv
      0 <= i && i <= n@pre && 
      IntArray::ceil_shape(dest@pre, 0, i) * IntArray::undef_ceil(dest@pre, i, n@pre)
  */
  for (i = 0; i < n; ++i) {
    dest[i] = src[i];
  }
}

void array_concat(int * ret, int *a, int n, int *b, int m)
/*@ Require 0 <= n && 0 <= m && n + m < INT_MAX && IntArray::full_shape(a, n) * IntArray::full_shape(b, m) * IntArray::undef_full(ret, n + m)
    Ensure IntArray::full_shape(a, n) * IntArray::full_shape(b, m) * IntArray::full_shape(ret, n + m)
*/
{
  int i;
  /*@ Inv
      0 <= i && i <= n@pre && 
      IntArray::ceil_shape(ret@pre, 0, i) * IntArray::undef_ceil(ret@pre, i, n@pre + m@pre)
  */
  for (i = 0; i < n; ++i) {
    ret[i] = a[i];
  }
  /*@ Inv
      0 <= i && i <= m@pre && 
      IntArray::ceil_shape(ret@pre, 0, n@pre + i) * IntArray::undef_ceil(ret@pre, n@pre + i, n@pre + m@pre)
  */
  for (i = 0; i < m; ++i) {
    ret[n + i] = b[i];
  }
}

void array_swap(int *a, int *b, int n)
/*@ Require 0 <= n && n < INT_MAX && IntArray::full_shape(a, n) * IntArray::full_shape(b, n)
    Ensure IntArray::full_shape(a, n) * IntArray::full_shape(b, n)
*/
{
  int i;
  /*@ Inv
      0 <= i && i <= n@pre 
  */
  for (i = 0; i < n; ++i) {
    int tmp = a[i];
    a[i] = b[i];
    b[i] = tmp;
  }
}

void array_vector_sum(unsigned int *ret, unsigned int *a, unsigned int *b, int n)
/*@ Require 0 <= n && n < INT_MAX && UIntArray::full_shape(a, n) * UIntArray::full_shape(b, n) * UIntArray::undef_full(ret, n)
    Ensure UIntArray::full_shape(a, n) * UIntArray::full_shape(b, n) * UIntArray::full_shape(ret, n)
*/
{
  int i;
  /*@ Inv
      0 <= i && i <= n@pre && 
      UIntArray::ceil_shape(ret@pre, 0, i) * UIntArray::undef_ceil(ret@pre, i, n@pre)
  */
  for (i = 0; i < n; ++i) {
    ret[i] = a[i] + b[i];
  }
}

void pointwise_mul(unsigned int *a, unsigned int *b, unsigned int *c, int n)
/*@ Require 0 <= n && n < INT_MAX && UIntArray::full_shape(a, n) * UIntArray::full_shape(b, n) * UIntArray::undef_full(c, n)
    Ensure UIntArray::full_shape(a, n) * UIntArray::full_shape(b, n) * UIntArray::full_shape(c, n)
*/
{
  int i;
  /*@ Inv
      0 <= i && i <= n@pre &&
      UIntArray::ceil_shape(c@pre, 0, i) * UIntArray::undef_ceil(c@pre, i, n@pre)
  */
  for (i = 0; i < n; ++i) {
    c[i] = a[i] * b[i];
  }
}

int array_max(int *a, int n)
/*@ Require 0 <= n && n < INT_MAX && IntArray::full_shape(a, n)
    Ensure IntArray::full_shape(a, n)
*/
{
  int i;
  int max = -1;
  /*@ Inv
      exists v, max == v && 0 <= i && i <= n@pre
  */
  for (i = 0; i < n; ++i) {
    if (a[i] > max) {
      max = a[i];
    }
  }
  return max;
}

void memset(int *a, int n, int value)
/*@ Require 0 <= n && n < INT_MAX && IntArray::undef_full(a, n)
    Ensure IntArray::full_shape(a, n)
*/
{
  int i;
  /*@ Inv
      0 <= i && i <= n@pre &&
      IntArray::ceil_shape(a@pre, 0, i) * IntArray::undef_ceil(a@pre, i, n@pre)
  */
  for (i = 0; i < n; ++i) {
    a[i] = value;
  }
}

struct list* malloc_list(int data)
/*@ With data0 
    Require data == data0 && emp
    Ensure __return != 0 && __return -> data == data0 && __return -> next == 0
*/;

struct list *array_to_list(int *a, int n)
/*@ Require 0 <= n && n < INT_MAX && IntArray::full_shape(a, n)
    Ensure listrep(__return) * IntArray::full_shape(a, n)
*/
{
  struct list *head = malloc_list(0);
  struct list *tail = head;
  int i;
  /*@ Inv exists v, 
      0 <= i && i <= n@pre && head != 0 && tail != 0 && tail -> data == v && tail -> next == 0 &&
      lseg(head, tail)
  */
  for (i = 0; i < n; ++i) {
    struct list *node = malloc_list(a[i]);
    tail->next = node;
    tail = node;
  }
  return head;
}