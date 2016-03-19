#include <stdlib.h>
#include <stdio.h>
#include <math.h>
#include <string.h>
#include <assert.h>
#include <ctype.h>

#define SIGN_OF(a) (((a) < 0) ? -1 : 1)
#define pyobj_to_bool(v) (!is_false(v))
#define logic_and(A, B) bool_to_pyobj(pyobj_to_bool(A) && pyobj_to_bool(B))
#define logic_or(A, B) bool_to_pyobj(pyobj_to_bool(A) || pyobj_to_bool(B))


enum type_tag { INT, FLOAT, BOOL, LIST, DICT, NONE , INVALID};

struct pyobj_struct;

struct array_struct {
	struct pyobj_struct* data;
	unsigned int len;
};

typedef struct array_struct array;


struct dict_struct {
	struct pyobj_struct* key;
	struct pyobj_struct* value;
	struct dict_struct* next;
};

typedef struct dict_struct dict;

struct pyobj_struct {
	enum type_tag tag;
	union {
		int i;                /* int */
		double f;             /* float */
		char b;               /* bool */
		array l;              /* list */
		dict* d;              /* dict */
	} u;
};
typedef struct pyobj_struct pyobj;

pyobj None = {NONE};

static int is_false(pyobj v);

pyobj less(pyobj a, pyobj b);
pyobj less_equal(pyobj a, pyobj b);
pyobj greater(pyobj a, pyobj b);
pyobj greater_equal(pyobj a, pyobj b);
pyobj equal(pyobj a, pyobj b);
pyobj not_equal(pyobj a, pyobj b);
pyobj identical(pyobj lhs, pyobj rhs);
pyobj contains(pyobj lhs, pyobj rhs);
pyobj add(pyobj lhs, pyobj rhs);
int find_key(pyobj dict, pyobj key);

pyobj make_list(pyobj len);
pyobj make_dict();
static enum {LINE_INITIAL, LINE_CONTINUED, LINE_NEW} line_state = LINE_INITIAL;
#define handle_continued(end) { \
		if (line_state == LINE_CONTINUED) {\
			if (end) \
			putchar ('\n'); \
			else \
			putchar (' '); \
		} else if (line_state == LINE_NEW)\
		putchar ('\n'); \
}
static void print(pyobj v);


char printed_0;
char printed_0_neg;
void print_float(double in)
{
	char outstr[128];

	snprintf(outstr, 128, "%.12g", in);

	char *p = outstr;

	if(in == 0.0)
	{
		if(printed_0 == 0)
		{
			printed_0 = 1;
			printed_0_neg = *p == '-'; //see if we incremented for negative
		}
		else
		{
			printf(printed_0_neg ? "-0.0" : "0.0");
			return;
		}
	}

	if(*p == '-')
		p++;


	while(*p && isdigit(*p))
		p++;

	printf( ( (*p)  ? "%s" : "%s.0" ), outstr);
}

void print_int(int i) {
	printf("%d", i);
}

void print_bool(char b) {
	if (b == 0)
		printf("False");
	else
		printf("True");
}

static pyobj *current_list;
static void print_list(pyobj pyobj_list)
{
	if(current_list && current_list == pyobj_list.u.l.data)
	{
		printf("[...]");
		return;
	}

	int will_reset = 0;
	if(!current_list)
	{
		current_list = pyobj_list.u.l.data;
		will_reset = 1;
	}

	array l = pyobj_list.u.l;
	printf("[");
	unsigned int i;
	for(i = 0; i < l.len; i++)
	{
		if (l.data[i].tag == LIST && l.data[i].u.l.data == l.data)
			printf("[...]");
		else
			print(l.data[i]);
		if(i != l.len - 1)
			printf(", ");
	}
	printf("]");

	if(will_reset)
		current_list = NULL;
}


static void print(pyobj v) {
	switch (v.tag) {
	case INT:
		print_int(v.u.i);
		break;
	case FLOAT: {
		print_float(v.u.f);
		break;
	}
	case BOOL:
		print_bool(v.u.b);
		break;
	case LIST: {
		print_list(v);
		break;
	}
	case NONE:
		printf ("None");
		break;
	default:
		printf("error, unhandled case in print\n");
		exit (1);
	}
}

pyobj int_to_pyobj(int x) {
	pyobj v;
	v.tag = INT;
	v.u.i = x;
	return v;
}

pyobj float_to_pyobj(double x) {
	pyobj v;
	v.tag = FLOAT;
	v.u.f = x;
	return v;
}

pyobj bool_to_pyobj(char x) {
	pyobj v;
	v.tag = BOOL;
	v.u.b = x;
	return v;
}

pyobj make_list(pyobj len) {
	pyobj v;
	assert (len.tag == INT);
	v.tag = LIST;
	v.u.l.data = (pyobj*)malloc(sizeof(pyobj) * len.u.i);
	v.u.l.len = len.u.i;
	return v;
}

pyobj make_dict() {
	pyobj v;
	v.tag = DICT;
	v.u.d = (dict*)malloc(sizeof(dict));
	v.u.d->key = (pyobj*)malloc(sizeof(pyobj));
	v.u.d->value = (pyobj*)malloc(sizeof(pyobj));
	v.u.d->next = NULL;
	return v;
}

pyobj* list_nth(pyobj list, pyobj n) {
	switch (list.tag) {
	case LIST: {
		switch (n.tag) {
		case INT: {
			if (n.u.i < 0 || (unsigned int)n.u.i < list.u.l.len)
				return &(list.u.l.data[n.u.i]);
			else {
				printf("ERROR: list_nth index larger than list");
				exit(1);
			}
		}
		case BOOL: {
			unsigned int idx = n.u.b ? 1u : 0u;
			if (idx < list.u.l.len)
				return &(list.u.l.data[idx]);
			else {
				printf("ERROR: list_nth index larger than list");
				exit(1);
			}
		}
		default:
			printf("ERROR: list_nth expected integer index");
			exit(1);
		}
	}
	default:
		printf("ERROR: list_nth applied to non-list");
		exit(1);
	}
}

int dict_len(dict* dictionary)
{
	dict** current_node = &dictionary;

	int count = 0;
	while(*current_node != NULL)
		{
			current_node = &(*current_node)->next;
			count++;
		}
	return count;
}

pyobj* dict_lookup(pyobj dictionary, pyobj n) {
	dict** current_node = &dictionary.u.d;

	if (dictionary.tag != DICT) {
		printf("ERROR: dict_lookup applied to non-dict");
		exit(1);
	}
	while(*current_node != NULL && pyobj_to_bool(not_equal(*(*current_node)->key, n)))
	{
		current_node = &(*current_node)->next;
	}
	if(*current_node == NULL)
	{
		*current_node = malloc(sizeof(dict));
		(*current_node)->next = NULL;
		(*current_node)->key = &n;
		(*current_node)->value->tag=INVALID;
	}
	return (*current_node)->value;
}

pyobj list_add(pyobj x, pyobj y) {
	array a = x.u.l;
	array b = y.u.l;
	pyobj v;
	unsigned int i;
	v.tag = LIST;
	v.u.l.data = (pyobj*)malloc(sizeof(pyobj) * (a.len + b.len));
	v.u.l.len = a.len + b.len;
	for (i = 0; i != a.len; ++i)
		v.u.l.data[i] = a.data[i];
	for (i = 0; i != b.len; ++i)
		v.u.l.data[a.len + i] = b.data[i];
	return v;
}

pyobj list_sub(pyobj x, pyobj y) {
	printf("error, unsupported operand types");
	exit (1);
}

pyobj list_mult(pyobj x, int n) {
	int i;
	pyobj r = make_list(int_to_pyobj(0));
	for (i = 0; i != n; ++i)
		r = list_add(x, r);
	return r;
}

pyobj logic_not(pyobj v);
pyobj list_or (pyobj x, pyobj y) {
	if (pyobj_to_bool (logic_not (x)))
		return y;
	return x;
}

pyobj list_mul(pyobj x, pyobj y) {
	switch (x.tag) {
	case INT:
		switch (y.tag) {
		case LIST:
			return list_mult(y, x.u.i);
		default:
			printf("error, unsupported operand types");
			exit (1);
		}
		case BOOL:
			switch (y.tag) {
			case LIST:
				return list_mult(y, x.u.b);
			default:
				printf("error, unsupported operand types");
				exit (1);
			}
			case LIST:
				switch (y.tag) {
				case INT:
					return list_mult(x, y.u.i);
				case BOOL:
					return list_mult(x, y.u.b);
				default:
					printf("error, unsupported operand types");
					exit (1);
				}
				default:
					printf("error, unsupported operand types");
					exit (1);
	}
}

static int is_false(pyobj v)
{
	switch (v.tag) {
	case INT:
		return v.u.i == 0;
	case FLOAT:
		return v.u.f == 0;
	case BOOL:
		return v.u.b == 0;
	case LIST:
		return v.u.l.len == 0;
	case DICT:
		return 0;
	default:
		printf("error, unhandled case in is_false\n");
		exit (1);
	}
}


pyobj* subscript(pyobj c, pyobj key)
{
	switch (c.tag) {
	case LIST:
		return list_nth(c, key);
	case DICT:
		return dict_lookup(c, key);
	default:
		printf("error in subscript, not a list or dictionary\n");
		exit (1);
	}
}

#define gen_unary_op(NAME, OP) \
		pyobj NAME(pyobj a) { \
	switch (a.tag) { \
	case INT: \
	return int_to_pyobj(OP a.u.i);                  \
	case FLOAT: \
	return float_to_pyobj(OP a.u.f);                \
	case BOOL: \
	return int_to_pyobj(OP a.u.b);                 \
	default: \
	printf("error, unhandled case in unary operator\n"); \
	exit (1); \
	} \
}

gen_unary_op(unary_add, +)
gen_unary_op(unary_sub, -)

#define gen_binary_op(NAME, OP) \
		pyobj NAME(pyobj a, pyobj b) { \
	switch (a.tag) { \
	case INT: \
	switch (b.tag) { \
	case INT: \
	return int_to_pyobj(a.u.i OP b.u.i); \
	case FLOAT: \
	return float_to_pyobj(a.u.i OP b.u.f); \
	case BOOL: \
	return int_to_pyobj(a.u.i OP b.u.b); \
	case LIST: \
	return list_##NAME(a, b); \
	default: \
	printf("error, unhandled case in operator\n"); \
	exit (1); \
	} \
	case FLOAT: \
	switch (b.tag) { \
	case INT: \
	return float_to_pyobj(a.u.f OP b.u.i); \
	case FLOAT: \
	return float_to_pyobj(a.u.f OP b.u.f); \
	case BOOL: \
	return float_to_pyobj(a.u.f OP b.u.b); \
	default: \
	printf("error, unhandled case in operator\n"); \
	exit (1); \
	} \
	case BOOL: \
	switch (b.tag) { \
	case INT: \
	return int_to_pyobj(a.u.b OP b.u.i); \
	case FLOAT: \
	return float_to_pyobj(a.u.b OP b.u.f); \
	case BOOL: \
	return int_to_pyobj(a.u.b OP b.u.b); \
	case LIST: \
	return list_##NAME(a, b); \
	default: \
	printf("error, unhandled case in operator\n"); \
	exit (1); \
	} \
	case LIST: \
	switch (b.tag) { \
	case LIST: \
	return list_##NAME(a, b); \
	case INT: \
	return list_##NAME(a, b); \
	case BOOL: \
	return list_##NAME(a, b); \
	default: \
	printf("error, unhandled case in operator\n"); \
	exit (1); \
	} \
	default: \
	printf("error, unhandled case in operator\n"); \
	exit (1); \
	} \
}

gen_binary_op(add, +)
gen_binary_op(sub, -)
gen_binary_op(mul, *)


pyobj logic_not(pyobj v)
{
	if (is_false(v))
		return bool_to_pyobj (1);
	else
		return bool_to_pyobj (0);
}

int min(int x, int y) { return y < x ? y : x; }

pyobj list_less(array x, array y) {
	int i;
	for (i = 0; i != min(x.len, y.len); ++i) {
		if (less(x.data[i], y.data[i]).u.b)
			return bool_to_pyobj (1);
		else if (less(y.data[i], x.data[i]).u.b)
			return bool_to_pyobj (0);
	}
	if (x.len < y.len)
		return bool_to_pyobj (1);
	else
		return bool_to_pyobj (0);
}
pyobj list_equal(array x, array y) {
	char eq = 1;
	int i;
	for (i = 0; i != min(x.len, y.len); ++i)
		eq = eq && equal(x.data[i], y.data[i]).u.b;
	if (x.len == y.len)
		return bool_to_pyobj (eq);
	else
		return bool_to_pyobj (0);
}
pyobj list_not_equal(array x, array y) {
	return logic_not(list_equal(x,y));
}
pyobj list_greater(array x, array y) {
	return list_less(y,x);
}
pyobj list_less_equal(array x, array y) {
	return logic_not (list_greater(y,x));
}
pyobj list_greater_equal(array x, array y) {
	return logic_not (list_less(y,x));
}

pyobj dict_less(dict* x, dict* y) {
	if(dict_len(x) < dict_len(y))
		return bool_to_pyobj(1);
	return bool_to_pyobj(0);
}
pyobj dict_equal(dict* x, dict* y) {
	dict** x_node = &x;
	dict** y_node = &y;

	if(dict_len(x) != dict_len(y))
		return bool_to_pyobj(0);
	while(*x_node != NULL && *y_node != NULL)
	{
		if((*x_node)->key != (*y_node)->key || (*x_node)->value != (*y_node)->value)
			return bool_to_pyobj(0);
	}
	if(*x_node != NULL || *y_node != NULL)
		return bool_to_pyobj(0);
	return bool_to_pyobj(1);
}

pyobj dict_not_equal(dict* x, dict* y) {
	return logic_not(dict_equal(x,y));
}
pyobj dict_greater(dict* x, dict* y) {
	return dict_less(y,x);
}
pyobj dict_less_equal(dict* x, dict* y) {
	return logic_not (dict_greater(y,x));
}
pyobj dict_greater_equal(dict* x, dict* y) {
	return logic_not (dict_less(y,x));
}

static pyobj none_less (pyobj a, pyobj b) {
	return bool_to_pyobj (b.tag != NONE);
}

static pyobj none_equal (pyobj a, pyobj b) {
	return bool_to_pyobj (a.tag == b.tag);
}

#define gen_comparison(NAME, OP) \
		pyobj NAME(pyobj a, pyobj b) \
		{\
	if (b.tag == NONE) \
	return none_##NAME (a, b); \
	switch (a.tag) {\
	case INT:\
	switch (b.tag) {\
	case INT:\
	return bool_to_pyobj (a.u.i OP b.u.i);        \
	case FLOAT:\
	return bool_to_pyobj (a.u.i OP b.u.f);         \
	case BOOL:\
	return bool_to_pyobj (a.u.i OP b.u.b);         \
	default: \
	return bool_to_pyobj (0); \
	}\
	case FLOAT: \
	switch (b.tag) {\
	case INT:\
	return bool_to_pyobj (a.u.f OP b.u.i);        \
	case FLOAT:\
	return bool_to_pyobj (a.u.f OP b.u.f);         \
	case BOOL:\
	return bool_to_pyobj (a.u.f OP b.u.b);         \
	default: \
	return bool_to_pyobj (0); \
	}\
	case BOOL: \
	switch (b.tag) {\
	case INT:\
	return bool_to_pyobj (a.u.b OP b.u.i);        \
	case FLOAT:\
	return bool_to_pyobj (a.u.b OP b.u.f);         \
	case BOOL:\
	return bool_to_pyobj (a.u.b OP b.u.b);         \
	default: \
	return bool_to_pyobj (0); \
	}\
	case LIST: \
	switch (b.tag) { \
	case LIST: \
	return list_##NAME(a.u.l, b.u.l);      \
	default: \
	return bool_to_pyobj (0);                      \
	} \
	case DICT: \
	switch (b.tag) { \
	case DICT: \
	return dict_##NAME(a.u.d, b.u.d); \
	default: \
	return bool_to_pyobj (0); \
	} \
	case NONE: \
	return none_##NAME (a, b);                       \
	default: \
	return bool_to_pyobj (0);                        \
	} \
		}

gen_comparison(less, <)
gen_comparison(equal, ==)

pyobj less_equal(pyobj a, pyobj b) {
	return logic_or (less(a,b), equal(a,b));
}

pyobj greater(pyobj a, pyobj b) {
	return logic_not (less_equal(a,b));
}

pyobj greater_equal(pyobj a, pyobj b) {
	return logic_not (less(a,b));
}

pyobj not_equal(pyobj a, pyobj b) {
	return logic_not (equal(a,b));
}

pyobj identical(pyobj a, pyobj b) {
	if(a.tag != b.tag)
		return bool_to_pyobj (0);
	switch(a.tag) {
	case INT:    return bool_to_pyobj (a.u.i == b.u.i);
	case BOOL:   return bool_to_pyobj (a.u.b == b.u.b);
	case FLOAT:  return bool_to_pyobj (a.u.f == b.u.f);
	case LIST:   return bool_to_pyobj (a.u.l.len == b.u.l.len && a.u.l.data == b.u.l.data);
	case DICT:	 return dict_equal(a.u.d, b.u.d);
	case NONE:   return bool_to_pyobj (1);
	case INVALID: return bool_to_pyobj (0);
	}
	return bool_to_pyobj (0);
}

pyobj contains(pyobj a, pyobj b) {
	switch (b.tag) {
	case LIST:
	{
		for (unsigned int i = 0; i < b.u.l.len; i++)
		{
			if (pyobj_to_bool(equal(*list_nth(b,int_to_pyobj((int)i)), a)))
			{
				return bool_to_pyobj (1);
			}
		}
	}
	case DICT:
	{
		for (unsigned int i = 0; i < dict_len(b.u.d); i++)
		{
			if (pyobj_to_bool(equal(*list_nth(b,int_to_pyobj((int)i)), a)))
			{
				return bool_to_pyobj (1);
			}
		}
	}
	return bool_to_pyobj (0);
	default:
		return bool_to_pyobj(0);
	}
}

