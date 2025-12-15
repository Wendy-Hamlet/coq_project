#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

int arr_sum(int n, int *a)
/*@ With l
    Require 0 < n && n < 100 && IntArray::full(a, n, l) && (forall (i: Z), (0 <= i && i < n) => (0 <= l[i] && l[i] < 100))
    Ensure  __return == sum(l) && IntArray::full(a, n, l) 
*/
{
  int i;
  i = 0;
  int ret;
  ret = 0;
  /*@ Inv
      0 <= i && i <= n && n == n@pre && ret == sum(sublist(0, i, l))
  */
  while (i < n) {
    ret += a[i];
    ++i;
  }
  return ret;
}

int arr_sum_do_while(int n, int *a)
/*@ With l
    Require 0 < n && n < 100 && IntArray::full(a, n, l) && (forall (i: Z), (0 <= i && i < n) => (0 <= l[i] && l[i] < 100))
    Ensure  __return == sum(l) && IntArray::full(a, n, l)
*/
{
  int i = 0;
  int ret = 0;
  do {
    ret += a[i];
    ++i;
  } /*@ Inv 0 <= i && i <= n && n == n@pre && ret == sum(sublist(0, i, l)) */ while (i != n);
  return ret;
}

int arr_sum_for(int n, int *a)
/*@ With l
    Require 0 < n && n < 100 && IntArray::full(a, n, l) && (forall (i: Z), (0 <= i && i < n) => (0 <= l[i] && l[i] < 100))
    Ensure  __return == sum(l) && IntArray::full(a, n, l)
*/
{
  int i;
  int ret = 0;
  /*@ Inv
      0 <= i && i <= n && n == n@pre && ret == sum(sublist(0, i, l))
  */
  for (i = 0; i < n; ++i) {
    ret += a[i];
  }
  return ret;
}

int arr_sum_which_implies(int n, int *a)
/*@ With l
    Require 0 < n && n < 100 && (forall (i: Z), (0 <= i && i < n) => (0 <= l[i] && l[i] < 100)) && IntArray::full(a, n, l)
    Ensure  __return == sum(l) && IntArray::full(a, n, l)
*/
{
  int i;
  int ret = 0;
  /*@ Inv
      0 <= i && i <= n@pre && ret == sum(sublist(0, i, l))
  */
  for (i = 0; i < n; ++i) {
    /*@ 0 <= i && i < n@pre && IntArray::full(a, n@pre, l) 
        which implies
        data_at(a + (i * sizeof(int)), int, l[i]) * IntArray::missing_i(a, i, 0, n@pre, l)
    */
    ret += a[i];
    /*@ 0 <= i && i < n@pre && data_at(a + (i * sizeof(int)), int, l[i]) * IntArray::missing_i(a, i, 0, n@pre, l)
        which implies
        0<= i && i < n@pre && IntArray::full(a, n@pre, l)
    */
  }
  return ret;
}

int arr_sum_update(int n, int *a)
/*@ With l
    Require 0 < n && n < 100 && (forall (i: Z), (0 <= i && i < n) => (0 <= l[i] && l[i] < 100)) && IntArray::full(a, n, l)
    Ensure  __return == sum(l) && IntArray::full(a, n, zeros(n))
*/
{
  int i;
  int ret = 0;
  /*@ Inv 
      0 <= i && i <= n@pre && n@pre == Zlength(l) && ret == sum(sublist(0, i, l)) && a == a@pre &&
      IntArray::full(a, n@pre, app(zeros(i), sublist(i, n@pre, l)))
  */
  for (i = 0; i < n; ++i) {
    /*@ 0 <= i && i < n@pre && a == a@pre && n@pre == Zlength(l) && IntArray::full(a, n@pre, app(zeros(i), sublist(i, n@pre, l))) 
        which implies
        a == a@pre && IntArray::missing_i(a, i, 0, n@pre, app(zeros(i), sublist(i, n@pre, l))) * data_at(a + (i * sizeof(int)), int, l[i])
    */
    ret += a[i];
    a[i] = 0;
    /*@ 0 <= i && i < n@pre && a == a@pre && n@pre == Zlength(l) && IntArray::missing_i(a, i, 0, n@pre, app(zeros(i), sublist(i, n@pre, l))) * data_at(a + (i * sizeof(int)), int, 0)
        which implies
        a == a@pre && IntArray::full(a, n@pre, app(zeros(i + 1), sublist(i + 1, n@pre, l)))
    */
  }
  return ret;
}


int arr_sum_pointer(int n, int *a)
/*@ With l
    Require 0 < n && n < 100 && IntArray::full(a, n, l) && (forall (i: Z), (0 <= i && i < n) => (0 <= l[i] && l[i] < 100))
    Ensure  __return == sum(l) && IntArray::full(a, n, l)
*/
{
  int i = 0;
  int ret = 0;
  int *endp = a + n;
  /*@ Inv
      0 <= i && i <= n && n == n@pre && ret == sum(sublist(0, i, l)) */
  while (endp - (a + i) != 0) {
    /*@ i != n */
    ret += *(a + i);
    ++i;
  }
  return ret;
}

