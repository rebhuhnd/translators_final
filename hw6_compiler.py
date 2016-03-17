#! /usr/bin/env python

import sys

logs = sys.stderr
import traceback
# import compiler
# from compiler.ast import *
from ast import *
import copy

debug = True


def prepend_stmts(ss, s):
    if isinstance(s, Expression):
        return Expression(ss + s.body)
    else:
        return Expression(ss + [s])


def append_stmts(s1, s2):
    if isinstance(s1, Expression):
        if isinstance(s2, Expression):
            return Expression(s1.nodes + s2.nodes)
        else:
            return Expression(s1.nodes + s2)
    elif isinstance(s2, Expression):
        return Expression([s1] + s2.nodes)
    else:
        return Expression([s1] + [s2])


# lhs : string, rhs : expr
def make_assign(lhs, rhs):
    # return Assign(nodes=[AssName(name=lhs, flags='OP_ASSIGN')], expr=rhs)
    return Assign(targets=[Name(id=lhs, ctx=Store())], value=rhs)


#############################################################################################
# Simplify comparison and logic operators

# New Classes for the Intermediate Representation that
# provide a uniform representation for binary and unary operations

class PrimitiveOp(AST):
    def __init__(self, name, nodes, lineno=None):
        self.name = name
        self.nodes = nodes
        self.lineno = lineno

    def getChildren(self):
        return self.nodes

    def getChildNodes(self):
        return self.nodes

    def __repr__(self):
        return "PrimitiveOp(%s, %s)" % (self.name, ', '.join([repr(e) for e in self.nodes]))


class Let(AST):
    def __init__(self, var, rhs, body, lineno=None):
        self.var = var
        self.rhs = rhs
        self.body = body
        self.lineno = lineno

    def getChildren(self):
        return self.rhs, self.body

    def getChildNodes(self):
        return self.rhs, self.body

    def __repr__(self):
        return "Let(%s, %s, %s)" % (repr(self.var), repr(self.rhs), repr(self.body))


# the following counter is for generating unique names
counter = 0


def generate_name(x):
    global counter
    name = x + str(counter)
    counter = counter + 1
    return name


binary_op_classes = [Add, Sub, Mult]
unary_op_classes = [UAdd, USub, Not]

class_to_fun = {Add: 'add', Sub: 'sub', Mult: 'mul',
                UAdd: 'unary_add', USub: 'unary_sub', Not: 'logic_not'}

compare_to_fun = {'<': 'less', '>': 'greater', '<=': 'less_equal', '>=': 'greater_equal',
                  '==': 'equal', '!=': 'not_equal', 'is': 'identical'}


# context is either 'expr' or 'lhs'
def simplify_ops(n, context='expr'):
    if isinstance(n, Module):
        return Module(body=map(simplify_ops, n.body))
    elif isinstance(n, Print):
        return Print(values=map(simplify_ops, n.values))
    elif isinstance(n, If):
        return If(test=simplify_ops(n.test), body=simplify_ops(n.body))  # no else
    elif isinstance(n, While):
        return While(test=simplify_ops(n.test), body=simplify_ops(n.body))  # no orelse
    elif isinstance(n, Assign):
        return Assign(targets=map(simplify_ops, n.targets), value=simplify_ops(n.value))
    elif n.__class__ in [Num, Name]:
        return n
    elif isinstance(n, UnaryOp):  # - or Not
        return PrimitiveOp(class_to_fun[n.op.__class__], map(simplify_ops, [n.operand]))
    elif isinstance(n, BinOp):  # +, -, *
        return PrimitiveOp(class_to_fun[n.op.__class__], map(simplify_ops, [n.left, n.right]))
    elif isinstance(n, BoolOp):  # And, Or
        return PrimitiveOp(class_to_fun[n.op.__class__], map(simplify_ops, n.values))
    elif isinstance(n, IfExp):
        return IfExp(test=simplify_ops(n.test), body=simplify_ops(n.body), orelse=simplify_ops(n.orelse))
    elif isinstance(n, Compare):
        operands = map(simplify_ops, [n.left] + n.comparators)  # left is the first operand!
        ops = map(lambda x: class_to_fun[x.__class__], n.ops)
        if len(ops) == 1:
            return PrimitiveOp(ops[0], operands)
        else:  # 3<5>4 => 3<5 and 5>4
            return PrimitiveOp('logic_and',
                               [PrimitiveOp(op, [x, y]) for op, x, y in zip(ops, operands, operands[1:])])
    elif isinstance(n, List):
        ls_name = generate_name('list')

        def gen_list(nodes, i):
            if len(nodes) == 0:
                return Name(id=ls_name)
            else:
                return Let('_', PrimitiveOp('assign', \
                                            [PrimitiveOp('deref', \
                                                         [PrimitiveOp('subscript', \
                                                                      [Name(id=ls_name), Num(n=i)]) \
                                                          ]), \
                                             simplify_ops(nodes[0])]), \
                           gen_list(nodes[1:], i + 1))

        return Let(ls_name, PrimitiveOp('make_list', [Num(n=len(n.elts))]), \
                   gen_list(n.elts, 0))
    elif isinstance(n, Subscript):  # Subscript(value=List(elts=[...]), slice=Index(value=Num(n=0)), ctx=Load()))
        return PrimitiveOp('deref', [PrimitiveOp('subscript', \
                                                 [simplify_ops(n.value), simplify_ops(n.slice.value)])])
    else:
        raise Exception('Error in simplify_ops: unrecognized AST node ' + repr(n))


###########################################################################################
# Convert to static single-assignment form (SSA)

def union(a, b):
    return a | b


def assigned_vars(n):
    # if isinstance(n, Stmt):
    #     return reduce(union, [assigned_vars(s) for s in n.nodes], set([]))
    if isinstance(n, Print):
        return set([])
    elif isinstance(n, Pass):
        return set([])
    elif isinstance(n, If):
        return reduce(union, [assigned_vars(b) for (c, b) in n.tests], set([])) \
               | assigned_vars(n.else_) \
               | (reduce(union, [assigned_vars(s) for s in n.phis], set([])) \
                      if hasattr(n, 'phis') else set([]))
    elif n == None:
        return set([])
    elif isinstance(n, Assign):
        return reduce(union, [assigned_vars(n) for n in n.nodes], set([]))
    # elif isinstance(n, AssName):
    #     return set([n.name])
    elif isinstance(n, While):
        return assigned_vars(n.body) \
               | (reduce(union, [assigned_vars(s) for s in n.phis], set([])) \
                      if hasattr(n, 'phis') else set([]))
    elif isinstance(n, Delete):
        return set([])
    else:
        return set([])


highest_version = {}


def get_high(x):
    if x in highest_version:
        v = highest_version[x] + 1
        highest_version[x] = v
        return v
    else:
        highest_version[x] = 0
        return 0


def get_current(current_version, x):
    if x in current_version:
        return current_version[x]
    else:
        return 0


def convert_to_ssa(t, current_version={}):
    if False:
        print >> logs, 'convert to ssa: ' + repr(t)
    if isinstance(t, Module):
        return Module(body=[convert_to_ssa(e, {}) for e in t.body])
    elif isinstance(t, Print):
        return Print(values=[convert_to_ssa(e, current_version) for e in t.values])
    elif isinstance(t, Num):
        return t
    elif isinstance(t, Name):
        if t.id in ['True', 'False']:
            return t
        else:
            return Name(id=t.id + '_' + str(get_current(current_version, t.id)))

    elif isinstance(t, PrimitiveOp):
        nodes = [convert_to_ssa(e, current_version) for e in t.nodes]
        return PrimitiveOp(t.name, nodes)

    elif isinstance(t, IfExp):
        new_test = convert_to_ssa(t.test, current_version)
        new_body = convert_to_ssa(t.body, current_version)
        new_orelse = convert_to_ssa(t.orelse, current_version)
        return IfExp(test=new_test, body=new_body, orelse=new_orelse)

    elif isinstance(t, If):
        new_tests = []
        for (cond, body) in t.tests:
            new_cond = convert_to_ssa(cond, current_version)
            body_cv = copy.deepcopy(current_version)
            new_body = convert_to_ssa(body, body_cv)
            new_tests.append((new_cond, new_body, body_cv))

        else_cv = copy.deepcopy(current_version)
        new_else = convert_to_ssa(t.else_, else_cv)

        assigned = reduce(union, [assigned_vars(b) for (c, b) in t.tests], set([])) \
                   | assigned_vars(t.else_)

        phis = []
        for x in assigned:
            current_version[x] = get_high(x)
            phi_rhs = [Name(x + '_' + str(get_current(cv, x))) for (_, _, cv) in new_tests]
            phi_rhs.append(Name(x + '_' + str(get_current(else_cv, x))))
            phi = make_assign(x + '_' + str(get_current(current_version, x)), \
                              PrimitiveOp('phi', phi_rhs))
            phis.append(phi)

        ret = If(tests=[(c, b) for (c, b, _) in new_tests], else_=new_else)
        ret.phis = phis
        return ret

    elif isinstance(t, While):
        pre_cv = copy.deepcopy(current_version)
        pre = Expression(nodes=[])
        if debug:
            print >> logs, 'convert to ssa While ', t.test
        assigned = assigned_vars(t.body)
        if debug:
            print >> logs, 'assigned = ', assigned
        for x in assigned:
            current_version[x] = get_high(x)

        body_cv = copy.deepcopy(current_version)
        new_body = convert_to_ssa(t.body, body_cv)

        new_test = convert_to_ssa(t.test, current_version)

        phis = []
        for x in assigned:
            body_var = Name(x + '_' + str(get_current(body_cv, x)))
            pre_var = Name(x + '_' + str(get_current(pre_cv, x)))
            phi = make_assign(x + '_' + str(get_current(current_version, x)), \
                              PrimitiveOp('phi', [pre_var, body_var]))
            phis.append(phi)

        ret = While(test=new_test, body=new_body, else_=None)
        ret.phis = phis
        return ret

    elif isinstance(t, Assign):
        new_rhs = convert_to_ssa(t.targets[0], current_version)
        new_nodes = []
        for n in t.targets:
            if isinstance(n, Name):
                x = n.id
                x_v = get_high(x)
                current_version[x] = x_v
                new_nodes.append(Name(id=x + '_' + str(x_v), ctx=n.ctx))
            else:
                new_nodes.append(convert_to_ssa(n, current_version))

        return Assign(targets=new_nodes, value=t.value)


    elif isinstance(t, Let):
        rhs = convert_to_ssa(t.body, current_version)
        v = get_high(t.var)
        current_version[t.var] = v
        body = convert_to_ssa(t.body, current_version)
        return Let(t.var + '_' + str(v), rhs, body)

    else:
        raise Exception('Error in convert_to_ssa: unrecognized AST node ' + repr(t))


#############################################################################################
# Insert variable declarations

class VarDecl(AST):
    def __init__(self, name, type, lineno=None):
        self.name = name
        self.type = type
        self.lineno = lineno

    def getChildren(self):
        return self.name, self.type

    def getChildNodes(self):
        return ()

    def __repr__(self):
        return "VarDecl(%s, %s)" % (self.name, self.type)


def insert_var_decls(n):
    if isinstance(n, Module):
        decls = [VarDecl(x, 'undefined') for x in assigned_vars(n.body)]
        # decls = [VarDecl(x,'undefined') for x in assigned_vars(n.node)]
        return Module(body=prepend_stmts(decls, n.body))
    else:
        raise Exception('Error in insert_var_decls: unhandled AST ' + repr(n))

        ###########################################################################################


# Type analysis, this pass annotates the IR in-place with types in the 'type' attribute

def join(t1, t2):
    if t1 == 'pyobj':
        return 'pyobj'
    elif t2 == 'pyobj':
        return 'pyobj'
    elif t1 == 'undefined':
        return t2
    elif t2 == 'undefined':
        return t1
    elif t1 == t2:
        return t1
    else:
        return 'pyobj'


arith_returns = {
    'int': 'int',
    'float': 'float',
    'pyobj': 'pyobj',
    'undefined': 'undefined'
}

arith_op = {
    ('int', 'int'): 'int',
    ('int', 'float'): 'float',
    ('int', 'bool'): 'int',
    ('int', 'pyobj'): 'pyobj',
    ('int', 'undefined'): 'undefined',
    ('float', 'int'): 'float',
    ('float', 'float'): 'float',
    ('float', 'bool'): 'float',
    ('float', 'pyobj'): 'pyobj',
    ('float', 'undefined'): 'undefined',
    ('bool', 'int'): 'int',
    ('bool', 'float'): 'float',
    ('bool', 'bool'): 'int',
    ('bool', 'pyobj'): 'pyobj',
    ('bool', 'undefined'): 'undefined',
    ('pyobj', 'int'): 'pyobj',
    ('pyobj', 'float'): 'pyobj',
    ('pyobj', 'bool'): 'pyobj',
    ('pyobj', 'pyobj'): 'pyobj',
    ('pyobj', 'undefined'): 'undefined',
    ('undefined', 'int'): 'undefined',
    ('undefined', 'float'): 'undefined',
    ('undefined', 'bool'): 'undefined',
    ('undefined', 'pyobj'): 'undefined',
    ('undefined', 'undefined'): 'undefined',
    ('pyobj',): 'pyobj',
    ('undefined',): 'undefined',
    ('int',): 'int',
    ('float',): 'float',
    ('bool',): 'int'
}

bool_returns = {
    'int': 'bool',
    'float': 'bool',
    'pyobj': 'bool',
    'bool': 'bool',
    'undefined': 'bool'
}

bool_op = {
    ('int', 'int'): 'int',
    ('int', 'float'): 'float',
    ('int', 'bool'): 'int',
    ('int', 'pyobj'): 'pyobj',
    ('int', 'undefined'): 'undefined',
    ('float', 'int'): 'float',
    ('float', 'float'): 'float',
    ('float', 'bool'): 'float',
    ('float', 'pyobj'): 'pyobj',
    ('float', 'undefined'): 'undefined',
    ('bool', 'int'): 'int',
    ('bool', 'float'): 'float',
    ('bool', 'bool'): 'bool',
    ('bool', 'pyobj'): 'pyobj',
    ('bool', 'undefined'): 'undefined',
    ('pyobj', 'int'): 'pyobj',
    ('pyobj', 'float'): 'pyobj',
    ('pyobj', 'bool'): 'pyobj',
    ('pyobj', 'undefined'): 'undefined',
    ('pyobj', 'pyobj'): 'pyobj',
    ('undefined', 'int'): 'undefined',
    ('undefined', 'float'): 'undefined',
    ('undefined', 'bool'): 'undefined',
    ('undefined', 'pyobj'): 'undefined',
    ('undefined', 'undefined'): 'undefined',
    ('undefined',): 'undefined',
    ('pyobj',): 'pyobj',
    ('int',): 'int',
    ('float',): 'float',
    ('bool',): 'bool'
}

arithop = (lambda ts: arith_op[ts])
boolop = (lambda ts: bool_op[ts])


def idop(ts):
    if ts[0] == ts[1]:
        return ts[0]
    else:
        return 'pyobj'


find_op_tag = {
    'add': arithop,
    'sub': arithop,
    'mul': arithop,
    'unary_add': arithop,
    'unary_sub': arithop,
    'logic_not': boolop,
    'logic_and': boolop,
    'logic_or': boolop,
    'equal': boolop,
    'not_equal': boolop,
    'less': boolop,
    'less_equal': boolop,
    'greater': boolop,
    'greater_equal': boolop,
    'identical': idop,
    'deref': (lambda ts: ''),
    'subscript': (lambda ts: 'pyobj'),
    'make_list': (lambda ts: ''),
    'assign': (lambda ts: reduce(join, ts, 'undefined')),
    'phi': (lambda ts: reduce(join, ts, 'undefined'))
}

arith_ret = (lambda ts: arith_returns[arith_op[ts]])
bool_ret = (lambda ts: bool_returns[bool_op[ts]])

op_returns = {
    'add': arith_ret,
    'sub': arith_ret,
    'mul': arith_ret,
    'unary_add': arith_ret,
    'unary_sub': arith_ret,
    'logic_not': bool_ret,
    'logic_and': bool_ret,
    'logic_or': bool_ret,
    'equal': bool_ret,
    'not_equal': bool_ret,
    'less': bool_ret,
    'less_equal': bool_ret,
    'greater': bool_ret,
    'greater_equal': bool_ret,
    'identical': bool_ret,
    'deref': (lambda ts: 'pyobj'),
    'subscript': (lambda ts: 'pyobj'),
    'make_list': (lambda ts: 'pyobj'),
    'assign': (lambda ts: reduce(join, ts, 'undefined')),
    'phi': (lambda ts: reduce(join, ts, 'undefined'))
}

type_changed = False


def get_var_type(env, x):
    if x in env:
        return env[x]
    else:
        return 'undefined'


# Don't need to do a join in update_var_type because the program
# is in SSA form. There is only one assignment to each variable.
def update_var_type(env, x, t):
    if x in env:
        if t == env[x]:
            return False
        else:
            env[x] = t
            return True
    else:
        env[x] = t
        return True


def predict_type(n, env):
    global type_changed

    if isinstance(n, Module):
        type_changed = True
        while type_changed:
            type_changed = False
            predict_type(n.body, env)

    elif isinstance(n, Print):
        for e in n.body:
            predict_type(e, env)

    elif isinstance(n, Delete):
        predict_type(n.expr, env)

    elif isinstance(n, If):
        for (cond, body) in n.tests:
            predict_type(cond, env)
            predict_type(body, env)
        predict_type(n.else_, env)
        for s in n.phis:
            predict_type(s, env)

    elif n == None:
        pass

    elif isinstance(n, While):
        predict_type(n.test, env)
        predict_type(n.body, env)
        for s in n.phis:
            predict_type(s, env)

    elif isinstance(n, Pass):
        pass

    elif isinstance(n, Assign):
        predict_type(n.targets, env)
        for a in n.targets:
            if isinstance(a, Name):
                type_changed += update_var_type(env, a.id, n.targets.type)
                a.type = get_var_type(env, a.id)
            else:
                predict_type(a, env)

    elif isinstance(n, VarDecl):
        n.type = get_var_type(env, n.name)

    # elif isinstance(n, Const):
    #     if isinstance(n.value, float):
    #         n.type = 'float'
    #     elif isinstance(n.value, int):
    #         n.type = 'int'
    #     else:
    #         raise Exception('Error in predict_type: unhandled constant ' + repr(n))

    elif isinstance(n, Name):
        if n.name == 'True' or n.name == 'False':
            n.type = 'bool'
        else:
            n.type = get_var_type(env, n.name)

    elif isinstance(n, PrimitiveOp):
        for e in n.nodes:
            predict_type(e, env)
        n.type = op_returns[n.name](tuple([e.type for e in n.nodes]))

    elif isinstance(n, IfExp):
        predict_type(n.test, env)
        predict_type(n.then, env)
        predict_type(n.else_, env)
        if n.then.type == n.else_.type:
            n.type = n.then.type
        else:
            n.type = 'pyobj'

    elif isinstance(n, Let):
        predict_type(n.rhs, env)
        body_env = copy.deepcopy(env)
        update_var_type(body_env, n.var, n.rhs.type)
        predict_type(n.body, body_env)
        n.type = n.body.type

    else:
        raise Exception('Error in predict_type: unrecognized AST node ' + repr(n))


###########################################################################################
# Type specialization
#   select specialized primitive operations
#   insert calls to is_true and make_* where appropriate

def convert_to_pyobj(e):
    if e.type != 'pyobj' and e.type != 'undefined':
        new_e = PrimitiveOp(e.type + '_to_pyobj', [e])
        new_e.type = 'pyobj'
        return new_e
    else:
        return e


def test_is_true(e):
    if e.type == 'pyobj':
        ret = PrimitiveOp('pyobj_to_bool', [e])
        ret.type = 'bool'
        return ret
    else:
        return e


def type_specialize(n):
    # print >> logs, 'type specialize ' + repr(n)
    if isinstance(n, Module):
        return Module(n.doc, type_specialize(n.node))
    elif isinstance(n, Expression):
        return Expression([type_specialize(s) for s in n.nodes])
    elif isinstance(n, Print):
        # would be nice to specialize print, but not a high priority
        return Print([convert_to_pyobj(type_specialize(e)) for e in n.nodes], n.dest)
    elif isinstance(n, Delete):
        return Delete(type_specialize(n.expr))
    elif isinstance(n, If):
        tests = [(test_is_true(type_specialize(cond)), type_specialize(body)) \
                 for (cond, body) in n.tests]
        else_ = type_specialize(n.else_)
        phis = [type_specialize(s) for s in n.phis]
        ret = If(tests, else_)
        ret.phis = phis
        return ret
    elif n == None:
        return None
    elif isinstance(n, While):
        test = test_is_true(type_specialize(n.test))
        body = type_specialize(n.body)
        phis = [type_specialize(s) for s in n.phis]
        ret = While(test, body, None)
        ret.phis = phis
        return ret
    elif isinstance(n, Pass):
        return n
    elif isinstance(n, Assign):
        expr = type_specialize(n.expr)
        nodes = [type_specialize(a) for a in n.nodes]
        if any([a.type == 'pyobj' for a in nodes]):
            expr = convert_to_pyobj(expr)
        return Assign(nodes, expr)

    # elif isinstance(n, AssName):
    #     return n

    elif isinstance(n, VarDecl):
        return n

    # elif isinstance(n, Const):
    #     return n
    elif isinstance(n, Name):
        return n
    elif isinstance(n, PrimitiveOp):
        nodes = [type_specialize(e) for e in n.nodes]
        tag = find_op_tag[n.name](tuple([e.type for e in n.nodes]))
        # if any([e.type == 'pyobj' for e in nodes]):
        if tag == 'pyobj':
            nodes = [convert_to_pyobj(e) for e in nodes]
        name = n.name if tag == '' else n.name + '_' + tag
        r = PrimitiveOp(name, nodes)
        r.type = n.type
        return r
    elif isinstance(n, IfExp):
        test = type_specialize(n.test)
        then = type_specialize(n.then)
        else_ = type_specialize(n.else_)
        test = test_is_true(test)
        if any([e.type == 'pyobj' for e in [n, then, else_]]):
            then = convert_to_pyobj(then)
            else_ = convert_to_pyobj(else_)
        r = IfExp(test, then, else_)
        r.type = n.type
        return r
    elif isinstance(n, Let):
        rhs = type_specialize(n.rhs)
        body = type_specialize(n.body)
        r = Let(n.var, rhs, body)
        r.type = n.type
        return r
    else:
        raise Exception('Error in type_specialize: unrecognized AST node ' + repr(n))


###########################################################################################
# Remove SSA

def split_phis(phis):
    branch_dict = {}
    for phi in phis:
        lhs = phi.nodes[0].name
        i = 0
        for rhs in phi.expr.nodes:
            if i in branch_dict:
                branch_dict[i].append(make_assign(lhs, rhs))
            else:
                branch_dict[i] = [make_assign(lhs, rhs)]
            i = i + 1
    return branch_dict


def remove_ssa(n):
    if isinstance(n, Module):
        return Module(n.doc, remove_ssa(n.node))
    elif isinstance(n, Expression):
        return Expression([remove_ssa(s) for s in n.nodes])
    elif isinstance(n, Print):
        return n
    elif isinstance(n, Delete):
        return n
    elif isinstance(n, If):
        tests = [(cond, remove_ssa(body)) for (cond, body) in n.tests]
        else_ = remove_ssa(n.else_)
        phis = [remove_ssa(s) for s in n.phis]
        branch_dict = split_phis(phis)
        if debug:
            print >> logs, 'remove ssa If '
            print >> logs, 'branch dict: ', branch_dict
        b = 0
        new_tests = []
        for (cond, body) in tests:
            if 0 < len(branch_dict):
                new_body = append_stmts(body, Expression(branch_dict[b]))
            else:
                new_body = body
            new_tests.append((cond, new_body))
            b = b + 1
        if 0 < len(branch_dict):
            new_else = append_stmts(else_, Expression(branch_dict[b]))
        else:
            new_else = else_
        ret = If(new_tests, new_else)
        return ret
    elif n == None:
        return None
    elif isinstance(n, While):
        test = n.test
        body = remove_ssa(n.body)
        phis = [remove_ssa(s) for s in n.phis]
        branch_dict = split_phis(phis)
        if debug:
            print >> logs, 'remove ssa While ', phis, branch_dict
        if 0 < len(branch_dict):
            ret = Expression(branch_dict[0] + [While(test, append_stmts(body, Expression(branch_dict[1])), None)])
        else:
            ret = While(test, body, None)
        return ret
    elif isinstance(n, Pass):
        return n
    elif isinstance(n, Assign):
        return Assign(n.nodes, n.expr)
    elif isinstance(n, VarDecl):
        return n
    else:
        raise Exception('Error in remove_ssa: unrecognized AST node ' + repr(n))


###########################################################################################
# Generate C output

python_type_to_c = {'int': 'int', 'bool': 'char', 'float': 'double', 'pyobj': 'pyobj',
                    'undefined': 'pyobj'}

skeleton = open("skeleton.c").readlines()


def generate_c(n):
    if isinstance(n, Module):
        return "".join(skeleton[:-2]) + generate_c(n.body) + "".join(skeleton[-2:])
    # elif isinstance(n, Expression):
    #     return '{' + '\n'.join([generate_c(e) for e in n.nodes]) + '}'
    elif isinstance(n, Print):
        space = 'printf(\" \");'
        newline = 'printf(\"\\n\");'
        nodes_in_c = ['print_%s(%s);' % (x.type, generate_c(x)) for x in n.values]
        return space.join(nodes_in_c) + newline
    elif isinstance(n, Delete):
        return generate_c(n.targets) + ';'
    elif isinstance(n, If):
        if n.else_ == None:
            else_ = ''
        else:
            else_ = 'else\n' + generate_c(n.else_)
        return 'if ' + '\n else if '.join(
            ['(%s)\n%s' % (generate_c(cond), generate_c(body)) for (cond, body) in n.tests]) + else_
    elif isinstance(n, While):
        return 'while (%s)\n%s' % (generate_c(n.test), generate_c(n.body))
    elif isinstance(n, Pass):
        return ';'
    elif isinstance(n, Assign):
        return '='.join([generate_c(v) for v in n.targets]) \
               + ' = ' + generate_c(n.value) + ';'
    elif isinstance(n, VarDecl):
        return '%s %s;' % (python_type_to_c[n.type], n.name)

        # elif isinstance(n, Const):
        # return repr(n.value)
    elif isinstance(n, Name):
        if n.name == 'True':
            return '1'
        elif n.name == 'False':
            return '0'
        else:
            return n.id
    elif isinstance(n, PrimitiveOp):
        if n.name == 'deref':
            return '*' + generate_c(n.nodes[0])
        elif n.name == 'assign_pyobj' or n.name == 'assign_int' or n.name == 'assign_bool' or n.name == 'assign_float':
            return '(' + generate_c(n.nodes[0]) + '=' + generate_c(n.nodes[1]) + ')'
        else:
            return n.name + '(' + ', '.join([generate_c(e) for e in n.nodes]) + ')'
    elif isinstance(n, IfExp):
        return '(' + generate_c(n.test) + ' ? ' \
               + generate_c(n.then) + ':' + generate_c(n.else_) + ')'
    elif isinstance(n, Let):
        t = python_type_to_c[n.rhs.type]
        rhs = generate_c(n.rhs)
        return '({ ' + t + ' ' + n.var + ' = ' + rhs + '; ' + generate_c(n.body) + ';})'
    elif n == None:
        return ''
    else:
        raise Exception('Error in generate_c: unrecognized AST node ' + repr(n))


######################### MAIN ##################################

if __name__ == "__main__":
    try:
        ast = parse("".join(sys.stdin.readlines()))
        if debug:
            print >> logs, dump(ast)
            print >> logs, 'simplifying ops --------------'
        ir = simplify_ops(ast)
        if debug:
            print >> logs, dump(ir)
            print >> logs, 'converting to ssa -----------'
            ir = convert_to_ssa(ir)
            if debug:
                print >> logs, dump(ir)
            print >> logs, 'predicting types -----------'
            predict_type(ir, {})
            if debug:
                print >> logs, dump(ir)
            #     print >> logs, 'type specialization -------'
            #     print >> logs, dump(ir)
            # ir = type_specialize(ir)
            # if debug:
            #     print >> logs, 'remove ssa ----------------'
            #     print >> logs, dump(ir)
            # ir = remove_ssa(ir)
            # if debug:
            #     print >> logs, 'finished remove ssa ------'
            #     print >> logs, dump(ir)
            #     print >> logs, 'generating C'
            # print generate_c(ir)
    except EOFError:
        print "Could not open file %s." % sys.argv[1]
    except Exception, e:
        print >> logs, "exception!"
        print >> logs, e
        traceback.print_exc(file=logs)

        exit(-1)
