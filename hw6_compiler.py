#! /usr/bin/env python

import sys
from ast import *
import copy
import traceback

logs = sys.stderr

debug = True


def prepend_stmts(ss, s):
    return ss + s


def append_stmts(s1, s2):
    return s1 + s2


# lhs : string, rhs : expr
def make_assign(lhs, rhs):
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

    def get_children(self):
        return self.nodes

    def get_child_nodes(self):
        return self.nodes

    def __repr__(self):
        return "PrimitiveOp(%s, %s)" % (self.name, ', '.join([repr(e) for e in self.nodes]))


class Let(AST):
    def __init__(self, var, rhs, body, lineno=None):
        self.var = var
        self.rhs = rhs
        self.body = body
        self.lineno = lineno

    def get_children(self):
        return self.rhs, self.body

    def get_child_nodes(self):
        return self.rhs, self.body

    def __repr__(self):
        return "Let(%s, %s, %s)" % (repr(self.var), repr(self.rhs), repr(self.body))


# the following counter is for generating unique names
counter = 0


def generate_name(x):
    global counter
    name = x + str(counter)
    counter += 1
    return name


binary_op_classes = [Add, Sub, Mult]
unary_op_classes = [UAdd, USub, Not]

class_to_fun = {Add: 'add', Sub: 'sub', Mult: 'mul',
                UAdd: 'unary_add', USub: 'unary_sub', Not: 'logic_not'}

compare_to_fun = {Lt: 'less', Gt: 'greater', LtE: 'less_equal', GtE: 'greater_equal',
                  Eq: 'equal', NotEq: 'not_equal', Is: 'identical'}


# context is either 'expr' or 'lhs'
def simplify_ops(n, context='expr'):
    if isinstance(n, list):
        # the actual Python list type, not an AST node representing a list
        return map(simplify_ops, n)
    elif isinstance(n, Module):
        return Module(body=map(simplify_ops, n.body))
    elif isinstance(n, Print):
        return Print(values=map(simplify_ops, n.values))
    elif isinstance(n, If):
        return If(test=simplify_ops(n.test), body=simplify_ops(n.body), orelse=simplify_ops(n.orelse))
    elif isinstance(n, While):
        return While(test=simplify_ops(n.test), body=simplify_ops(n.body), orelse=simplify_ops(n.orelse))
    elif isinstance(n, Assign):
        return Assign(targets=map(simplify_ops, n.targets), value=simplify_ops(n.value, 'lhs'))
    elif n.__class__ in [Num, Name]:
        return n
    elif isinstance(n, UnaryOp):  # - or Not
        return PrimitiveOp(class_to_fun[n.op.__class__], map(simplify_ops, [n.operand]))
    elif isinstance(n, BinOp):  # +, -, *
        name = class_to_fun[n.op.__class__]
        left = simplify_ops(n.left)
        l_name = generate_name('left')
        right = simplify_ops(n.right)
        return Let(l_name, left, PrimitiveOp(name, [Name(l_name, Load()), right]))
    elif isinstance(n, BoolOp):  # And, Or
        return PrimitiveOp(class_to_fun[n.op.__class__], map(simplify_ops, n.values))
    elif isinstance(n, IfExp):
        return IfExp(test=simplify_ops(n.test), body=simplify_ops(n.body), orelse=simplify_ops(n.orelse))
    elif isinstance(n, Compare):
        operands = map(simplify_ops, [n.left] + n.comparators)  # left is the first operand!
        ops = map(lambda x: compare_to_fun[x.__class__], n.ops)
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
                return Let('_', PrimitiveOp('assign',
                                            [PrimitiveOp('deref',
                                                         [PrimitiveOp('subscript',
                                                                      [Name(id=ls_name), Num(n=i)])
                                                          ]),
                                             simplify_ops(nodes[0])]),
                           gen_list(nodes[1:], i + 1))

        return Let(ls_name, PrimitiveOp('make_list', [Num(n=len(n.elts))]),
                   gen_list(n.elts, 0))
    elif isinstance(n, Subscript):  # Subscript(value=List(elts=[...]), slice=Index(value=Num(n=0)), ctx=Load()))
        return PrimitiveOp('deref', [PrimitiveOp('subscript',
                                                 [simplify_ops(n.value), simplify_ops(n.slice.value)])])
    elif isinstance(n, FunctionDef):
        return FunctionDef(name=n.name, args=n.args, decorator_list=n.decorator_list, body=map(simplify_ops, n.body))
    elif isinstance(n, Expr):
        return Expr(value=simplify_ops(n.value))
    elif isinstance(n, Return):
        return Return(value=simplify_ops(n.value))
    
    elif isinstance(n, Call):
        return Call(func=simplify_ops(n.func), args=n.args, keywords=n.keywords, starargs=n.starargs, kwargs=n.kwargs)

    else:
        raise Exception('Error in simplify_ops: unrecognized AST node ' + repr(n) + dump(n))


###########################################################################################
# Convert to static single-assignment form (SSA)

def union(a, b):
    return a | b


def assigned_vars(n):
    if isinstance(n, Module):
        return assigned_vars(n.body)
    elif isinstance(n, list):
        # the actual Python list type, not an AST node representing a list
        return reduce(union, map(assigned_vars, n), set([]))
    elif isinstance(n, Print):
        return set([])
    elif isinstance(n, Pass):
        return set([])
    elif isinstance(n, If):
        return assigned_vars(n.body) \
               | assigned_vars(n.orelse) \
               | (reduce(union, [assigned_vars(s) for s in n.phis], set([]))
                  if hasattr(n, 'phis') else set([]))
    elif n is None:
        return set([])
    elif isinstance(n, Assign):
        return reduce(union, [assigned_vars(n) for n in n.targets], set([]))
    elif isinstance(n, Name) and isinstance(n.ctx, Store):
        return set([n.id])
    elif isinstance(n, While):
        return assigned_vars(n.body) \
               | (reduce(union, [assigned_vars(s) for s in n.phis], set([]))
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
    if isinstance(t, list):
        # the actual Python list type, not an AST node representing a list
        return [convert_to_ssa(e, current_version) for e in t]
    elif isinstance(t, Module):
        return Module(body=convert_to_ssa(t.body, {}))
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
        new_test = convert_to_ssa(t.test, current_version)
        body_cv = copy.deepcopy(current_version)
        new_body = convert_to_ssa(t.body, body_cv)
        else_cv = copy.deepcopy(current_version)
        new_orelse = convert_to_ssa(t.orelse, else_cv)

        assigned = assigned_vars(t.body) | assigned_vars(t.orelse)

        phis = []
        for x in assigned:
            current_version[x] = get_high(x)
            phi_rhs = [Name(x + '_' + str(get_current(body_cv, x)), Store()),
                       Name(x + '_' + str(get_current(else_cv, x)), Store())]
            phi = make_assign(x + '_' + str(get_current(current_version, x)),
                              PrimitiveOp('phi', phi_rhs))
            phis.append(phi)

        ret = If(test=new_test, body=new_body, orelse=new_orelse)
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
            body_var = Name(x + '_' + str(get_current(body_cv, x)), Load())
            pre_var = Name(x + '_' + str(get_current(pre_cv, x)), Load())
            phi = make_assign(x + '_' + str(get_current(current_version, x)),
                              PrimitiveOp('phi', [pre_var, body_var]))
            phis.append(phi)

        ret = While(test=new_test, body=new_body, else_=None)
        ret.phis = phis
        return ret

    elif isinstance(t, Assign):
        new_rhs = convert_to_ssa(t.value, current_version)
        new_nodes = []
        for n in t.targets:
            if isinstance(n, Name):
                x = n.id
                x_v = get_high(x)
                current_version[x] = x_v
                new_nodes.append(Name(id=x + '_' + str(x_v), ctx=n.ctx))
            else:
                new_nodes.append(convert_to_ssa(n, current_version))

        return Assign(targets=new_nodes, value=new_rhs)

    elif isinstance(t, Let):
        rhs = convert_to_ssa(t.rhs, current_version)
        v = get_high(t.var)
        current_version[t.var] = v
        body = convert_to_ssa(t.body, current_version)
        return Let(t.var + '_' + str(v), rhs, body)

    elif isinstance(t, FunctionDef):
        name = t.name
        name_v = get_high (name)
        current_version[name] = name_v
        return FunctionDef(name=t.name + '_' + str(name_v), args=t.args, decorator_list=t.decorator_list, body=map(convert_to_ssa, t.body))

    elif isinstance(t, Expr):
        return Expr(value=convert_to_ssa(t.value, current_version))
    
    elif isinstance(t, Call):
        return Call(func=convert_to_ssa(t.func, current_version), args=t.args, keywords=t.keywords, starargs=t.starargs, kwargs=t.kwargs)
    
    elif isinstance(t, Return):
        return Return(value=convert_to_ssa(t.value, current_version))

    else:
        raise Exception('Error in convert_to_ssa: unrecognized AST node ' + repr(t))


#############################################################################################
# Insert variable declarations

class VarDecl(AST):
    def __init__(self, name, type, lineno=None):
        self.name = name
        self.type = type
        self.lineno = lineno

    def get_children(self):
        return self.name, self.type

    def get_child_nodes(self):
        return ()

    def __repr__(self):
        return "VarDecl(%s, %s)" % (self.name, self.type)


def insert_var_decls(n):
    if isinstance(n, Module):
        assigned_for_main = []
        body = []
        for x in n.body:
            if isinstance (x, FunctionDef):
                decls = [VarDecl(y, 'undefined') for y in assigned_vars (x.body)]
                body.append (FunctionDef(name=x.name, args=x.args, decorator_list=x.decorator_list, body=prepend_stmts (decls, x.body))) 
            else:
                body.append (x)
                assigned_for_main += list (assigned_vars (x))
        decls = [VarDecl(x, 'undefined') for x in assigned_for_main]
        return Module(body=prepend_stmts(decls, body))
    else:
        raise Exception('Error in insert_var_decls: unhandled AST ' + repr(n))

        ###########################################################################################


###########################################################################################
# Remove SSA

def split_phis(phis):
    branch_dict = {}
    for phi in phis:
        lhs = phi.targets[0].id
        i = 0
        for rhs in phi.value.nodes:
            if i in branch_dict:
                branch_dict[i].append(make_assign(lhs, rhs))
            else:
                branch_dict[i] = [make_assign(lhs, rhs)]
            i += 1
    return branch_dict


def remove_ssa(n):
    if isinstance(n, list):
        # the actual Python list type, not an AST node representing a list
        return map(remove_ssa, n)
    elif isinstance(n, Module):
        return Module(remove_ssa(n.body))
    elif isinstance(n, Expression):
        return Expression([remove_ssa(s) for s in n.nodes])
    elif isinstance(n, Print):
        return n
    elif isinstance(n, Delete):
        return n
    elif isinstance(n, If):
        test = n.test
        body = remove_ssa(n.body)
        orelse = remove_ssa(n.orelse)
        phis = [remove_ssa(s) for s in n.phis]
        branch_dict = split_phis(phis)
        if debug:
            print >> logs, 'remove ssa If '
            print >> logs, 'branch dict: ', branch_dict
        new_tests = []
        if len(branch_dict):
            new_body = append_stmts(body, branch_dict[0])
            new_orelse = append_stmts(orelse, branch_dict[1])
        else:
            new_body = body
            new_orelse = orelse
        ret = If(test, new_body, new_orelse)
        return ret
    elif n is None:
        return None
    elif isinstance(n, While):
        test = n.test
        body = remove_ssa(n.body)
        phis = [remove_ssa(s) for s in n.phis]
        branch_dict = split_phis(phis)
        if debug:
            print >> logs, 'remove ssa While ', phis, branch_dict
        if 0 < len(branch_dict):
            ret = Expression(branch_dict[0] + [While(test, append_stmts(body, branch_dict[1]), None)])
        else:
            ret = While(test, body, None)
        return ret
    elif isinstance(n, Pass):
        return n

    elif isinstance(n, Assign):
        return Assign(n.targets, n.value)

    elif isinstance(n, VarDecl):
        return n

    elif isinstance(n, FunctionDef):
        return FunctionDef(name=n.name, args=n.args, decorator_list=n.decorator_list, body=map(remove_ssa, n.body))

    elif isinstance(n, Expr):
        return n
    
    elif isinstance(n, Call):
        return Call(func=remove_ssa(n.func), args=n.args, keywords=n.keywords, starargs=n.starargs, kwargs=n.kwargs)
    
    elif isinstance(n, Return):
        return n
    
    elif isinstance(n, Num):
        return n

    elif isinstance(n, Name):
        return n

    else:
        raise Exception('Error in remove_ssa: unrecognized AST node ' + repr(n) + dump(n))


###########################################################################################
# Generate C output
skeleton = open("skeleton.c").read()


def generate_c(n):
    if isinstance(n, Module):
        return "int main (int argc, const char *argv[]) {" + generate_c(n.body) + "return 0;}"
    elif isinstance(n, list):
        # the actual Python list type, not an AST node representing a list
        return '{' + '\n'.join(map(generate_c, n)) + '}'
    elif isinstance(n, Expression):
        return '{' + '\n'.join([generate_c(e) for e in n.body]) + '}'
    elif isinstance(n, Print):
        space = 'printf(\" \");'
        newline = 'printf(\"\\n\");'
        nodes_in_c = ['print(%s);' % generate_c(x) for x in n.values]
        return space.join(nodes_in_c) + newline
    elif isinstance(n, Delete):
        return generate_c(n.targets) + ';'
    elif isinstance(n, If):
        if len(n.orelse) == 0:
            else_ = ''
        else:
            else_ = 'else\n' + generate_c(n.orelse)
        return 'if (pyobj_to_bool (%s))\n%s' % (generate_c(n.test), generate_c(n.body)) + else_
    elif isinstance(n, While):
        return 'while (pyobj_to_bool (%s))\n%s' % (generate_c(n.test), generate_c(n.body))
    elif isinstance(n, Pass):
        return ';'
    elif isinstance(n, Assign):
        return '='.join([generate_c(v) for v in n.targets]) \
               + ' = ' + generate_c(n.value) + ';'
    elif isinstance(n, VarDecl):
        return 'pyobj %s;' % n.name

    elif isinstance(n, Num):
        return type(n.n).__name__ + "_to_pyobj (%s)" % n.n
    elif isinstance(n, Name):
        if n.id == 'True':
            return 'bool_to_pyobj (1)'
        elif n.id == 'False':
            return 'bool_to_pyobj (0)'
        else:
            return n.id
    elif isinstance(n, PrimitiveOp):
        if n.name == 'deref':
            return '*' + generate_c(n.nodes[0])
        elif n.name == 'assign':
            return '(' + generate_c(n.nodes[0]) + '=' + generate_c(n.nodes[1]) + ')'
        else:
            return n.name + '(' + ', '.join([generate_c(e) for e in n.nodes]) + ')'
    elif isinstance(n, IfExp):
        return '(' + generate_c(n.test) + ' ? ' \
               + generate_c(n.then) + ':' + generate_c(n.else_) + ')'
    elif isinstance(n, Let):
        rhs = generate_c(n.rhs)
        return '({ pyobj ' + n.var + ' = ' + rhs + '; ' + generate_c(n.body) + ';})'
    elif isinstance(n, FunctionDef):
        return ""
    elif isinstance(n, Expr):
        return generate_c(n.value) + ";"
    elif isinstance(n, Call):
        return generate_c(n.func) + "()"
    elif isinstance(n, Return):
        return "return (%s);" % generate_c (n.value)
    elif n is None:
        return ''
    else:
        raise Exception('Error in generate_c: unrecognized AST node ' + repr(n) + dump(n))

def get_prototype (funcdef):
    
    return "pyobj %s()" % funcdef.name

def get_prototypes (n):
    assert isinstance (n, Module)
    
    for n in n.body:
        
        if isinstance (n, FunctionDef):
            print get_prototype (n) + ";\n"    

def get_functions (n):
    assert isinstance (n, Module)
    
    for n in n.body:
        
        if isinstance (n, FunctionDef):
            print "%s\n{%s return int_to_pyobj (0);}" % (get_prototype (n), generate_c (n.body))


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
            print >> logs, 'inserting var decls ---------'
        ir = insert_var_decls(ir)
        if debug:
            print >> logs, 'remove ssa ----------------'
            print >> logs, dump(ir)
        ir = remove_ssa(ir)
        if debug:
            print >> logs, 'finished remove ssa ------'
            print >> logs, dump(ir)
            print >> logs, 'generating C'
        print skeleton
        get_prototypes (ir)
        get_functions (ir)
        print generate_c(ir)
    except EOFError:
        print "Could not open file %s." % sys.argv[1]
    except Exception, e:
        print >> logs, "exception!"
        print >> logs, e
        traceback.print_exc(file=logs)

        exit(-1)
