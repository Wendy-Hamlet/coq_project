struct sll {
    unsigned int data;
    struct sll * next;
};

struct sllb {
    struct sll * head;
    struct sll ** ptail;
};

struct sllb * nil_list_box();
struct sllb * cons_list_box(unsigned int, struct sllb *);
void free_list_box(struct sllb *);
struct sllb * app_list_box(struct sllb *, struct sllb *);
struct sllb * map_list_box(struct sllb *, unsigned int);
unsigned int sllb2array(struct sllb *, unsigned int **);
// the return value is length

/* The following is not needed to verify */
struct sll * new_list_node();
struct sllb * new_sllb();
unsigned int * new_uint_array(unsigned int);
void free_list_node(struct sll *);
void free_sllb(struct sllb * );