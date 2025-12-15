#include "sll_lib.h"

struct sll * nil_list()
/*@ Require 
    Ensure  */
{
    return (struct sll *) 0;
}

struct sll * cons_list(unsigned int data, struct sll * next)
{
    struct sll * node = new_list_node();
    node -> data = data;
    node -> next = next;
    return node;
}

void free_list(struct sll * head)
{
    while (head) {
        struct sll * tmp = head;
        head = head -> next;
        free_list_node(tmp);
    }
}

void map_list(struct sll * head, unsigned int x)
{
    struct sll * p;
    for (p = head; p != (struct sll *) 0; p = p -> next)
        p -> data = x * p -> data;
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
