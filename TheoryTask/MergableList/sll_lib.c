#include "../qcp-binary-democases/QCP_examples/verification_stdlib.h"
#include "../qcp-binary-democases/QCP_examples/verification_list.h"
#include "../qcp-binary-democases/QCP_examples/sll_def.h"
#include "sll_lib.h"

/*@ Extern Coq (map_mult: Z -> list Z -> list Z) */

struct sll * nil_list()
/*@ Require emp
    Ensure sll(__return, nil)
*/
{
    return (struct sll *) 0;
}

struct sll * new_list_node()
/*@ Require emp
    Ensure __return != 0 &&
           store(&(__return -> data), 0) *
           store(&(__return -> next), 0)
*/;

struct sll * cons_list(unsigned int data, struct sll * next)
/*@ With l
    Require sll(next, l)
    Ensure sll(__return, cons(data, l))
*/ 
{
    struct sll * node = new_list_node();
    node -> data = data;
    node -> next = next;
    return node;
}

void free_list_node(struct sll * p)
/*@ Require emp
    Ensure emp
*/;

void free_list(struct sll * head)
/*@ With l
    Require sll(head, l)
    Ensure emp
*/
{
    /*@ Inv exists l_rest, sll(head, l_rest) */
    while (head) {
        /*@ exists l_rest, head != 0 && sll(head, l_rest)
            which implies
            exists l_rest_new, l_rest == cons(head->data, l_rest_new) && sll(head->next, l_rest_new)
        */
        struct sll * tmp = head;
        head = head -> next;
        free_list_node(tmp);
    }
}

void map_list(struct sll * head, unsigned int x)
/*@ With l
    Require sll(head, l)
    Ensure sll(head, map_mult(x, l))
*/
{
    struct sll * p;
    /*@ Inv exists l1 l2, l == app(l1, l2) && 
            sllseg(head, p, map_mult(x, l1)) * sll(p, l2)
    */
    for (p = head; p != (struct sll *) 0; p = p -> next) {
        /*@ exists l1 l2, l == app(l1, l2) && 
                sllseg(head, p, map_mult(x, l1)) * sll(p, l2) &&
                p != 0
            which implies
            exists l2_new, l2 == cons(p->data, l2_new) && 
                sllseg(head, p, map_mult(x, l1)) * sll(p->next, l2_new)
        */
        p -> data = x * p -> data;
    }
}   

struct sllb * nil_list_box()
{
    struct sllb * box = new_sllb();
    box -> head = nil_list();
    box -> ptail  = & box -> head;
    return box;
}

struct sllb * cons_list_box(unsigned int data, struct sllb * box)
{
    box -> head = cons_list(data, box -> head);
    if (box -> ptail == & box -> head)
    {
        box -> ptail = & (box -> head -> next);
    }
    return box;
}

struct sllb * map_list_box(struct sllb * box, unsigned int x)
{
    map_list(box -> head, x);
    return box;
}

void free_list_box(struct sllb * box)
{
    free_list(box -> head);
    free_sllb(box);
}

struct sllb * app_list_box(struct sllb * b1, struct sllb * b2)
{
    * (b1 -> ptail) = b2 -> head;
    if (b2 -> head != (struct sll *) 0)
    {
        b1 -> ptail = b2 -> ptail;
    }
    free_sllb(b2);
    return b1;
}

unsigned int sll_length(struct sll * head)
{
    unsigned int len = 0;
    while (head) {
        ++ len;
        head = head -> next;
    }
    return len;
}

unsigned int sll2array(struct sll * head, unsigned int ** out_array)
{
    unsigned int len = sll_length(head);
    unsigned int * arr = new_uint_array(len);
    unsigned int i = 0;
    struct sll * p;
    for (p = head; p; p = p -> next)
        arr[i++] = p -> data;
    * out_array = arr;
    return len;
}

unsigned int sllb2array(struct sllb * box, unsigned int ** out_array)
{
    return sll2array(box -> head, out_array);
}
