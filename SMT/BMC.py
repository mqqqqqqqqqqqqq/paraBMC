import os
import sys
import time
sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.append("\\home\\lyj238\\Mqian\\smt_dl\\smt4Inductive_Invariants\\protocols\\mutual_nodata_benchmark\\")
import murphi
import constructSMT
from z3 import *
import itertools
import subprocess
import re
from collections import defaultdict
import shutil
from murphiparser import *
import copy
from collections import Counter

from concurrent.futures import ThreadPoolExecutor
from multiprocessing import Process, Queue, Value

from protocols import *
# import cmurphi_LS

EnumType_vars = dict()
enum_value_map = dict()
all_vars = dict()
all_ins_vars = list()
all_LTL_vars = list()
const_pmurphi_map = dict()
all_pmurphi = dict()

inv_count = 0
str_murphi = ""

bmc_fomula_time = 0.0
bmc_check_time = 0.0

def defEnum(c):
    for enum_typ, enum_value in c.enum_typ_map.items():
        if enum_typ in enum_value_map.keys():
            # Skip if already defined
            pass
        else:
            assert isinstance(enum_value, murphi.EnumType)
            sub_enumValue = dict()
            enumDef = ""
            valueDef = []
            sub_enumValue[enum_typ] = z3.DatatypeSortRef
            for index, name in enumerate(enum_value.names):
                sub_enumValue[name] = z3.DatatypeRef
                if index == len(enum_value.names) - 1:
                    enumDef = enumDef + f"sub_enumValue[\"{name}\"]"
                else:
                    enumDef = enumDef + f"sub_enumValue[\"{name}\"], "
                valueDef.append(name)

            # Check if enum_typ is already defined
            if isinstance(sub_enumValue[enum_typ], z3.DatatypeSortRef):
                print(f"EnumSort for {enum_typ} is already defined.")
            else:
                exec_line = "sub_enumValue[enum_typ], " + "(" + enumDef + ")" + "=" + "EnumSort" + "(enum_typ, valueDef)"
                exec(exec_line)
                enum_value_map[enum_typ] = sub_enumValue

# 将 murphi 中的 var 变量定义为 smt 对应的变量
def setKey(expr, replacement, isbool=False, isdigit=False, isenum=False):
    global EnumType_vars
    if isbool:
        if replacement == "":
            return [Bool(str(expr) + replacement), expr]
        else:
            return [Bool(str(expr) + replacement)]
    elif isdigit:
        if replacement == "":
            return [Int(str(expr) + replacement), expr]
        else:
            return [Int(str(expr) + replacement)]
    elif isenum:
        if replacement == "":
            return [Const(str(expr) + replacement, enum_value_map[EnumType_vars[str(expr) + replacement]][
                EnumType_vars[str(expr) + replacement]]), expr]
        else:
            return [Const(str(expr) + replacement, enum_value_map[EnumType_vars[str(expr) + replacement]][
                EnumType_vars[str(expr) + replacement]])]
    else:
        print(str(expr), type(expr))
        if replacement == "":
            # print(str(expr), type(expr))
            return [z3.String(str(expr) + replacement), expr]
        else:
            return [z3.String(str(expr) + replacement)]

def join_z3_statements(statement):
        if len(statement) == 1:
            return statement[0]
        else:
            # return (str(statement[-1]) + "& (" + self.join_statements(statement[:-1]) + ")")
            return And(statement[-1], join_z3_statements(statement[:-1]))
        
def disjoin_z3_statements(statement):
        if len(statement) == 1:
            return statement[0]
        else:
            # return (str(statement[-1]) + "| (" + self.join_statements(statement[:-1]) + ")")
            return Or(statement[-1], disjoin_z3_statements(statement[:-1]))
       
        
class BMC_LTL_Formula():
    def __init__(self, protocol_name, boolVars, enum_typ_map, typ_map, scalarsetVars, 
                 upper_bound, lower_procount, upper_procount, name, init_state, axiom_ins, instance, inv_path, bmc_inv):
        self.protocol_name = protocol_name
        self.name = name
        self.inv_path = inv_path
        self.boolVars = boolVars
        self.Inv = bmc_inv

        self.Invvar = dict()
        self.Invformula = list()

        if init_state:
            self.init_state = init_state["Init"]

        self.axiom_ins = list()
        if axiom_ins:
            for axiom_name, axiom_for in axiom_ins.items():
                self.axiom_ins.append(axiom_for)

        if instance:
            self.guard = instance["guard"]
            # print("self.guard: ", self.guard)
            # assert isinstance(self.guard, murphi.OpExpr)

            self.assign = instance["assign"]
            # assert all(isinstance(f, murphi.AssignCmd) for f in self.assign)

            self.assumption = instance["assumption"]

        self.negInv = bmc_inv
        # print("self.negInv: ", self.negInv)
        # print("bmc_inv: ", bmc_inv)

        # self.inv = instance["inv"]

        self.enum_typ_map = enum_typ_map

        self.typ_map = typ_map

        self.scalarsetVars = scalarsetVars

        self.lower_procount = lower_procount
        self.upper_procount = upper_procount
        self.upper_bound = upper_bound

        self.dataVars = []

        self.initvar = dict()
        self.initformula = list()

        self.axiomvar = dict()
        self.axiomformula = list()

        self.guardvar = dict()
        self.guardformula = list()

        self.assignvar = dict()
        self.assignformula = list()

        self.assumptionvar = dict()
        self.assumptionformula = list()

        self.negInvvar = dict()
        self.negInvformula = list()

        self.variables = dict()
        self.boundStates = list()

        self.GADvar = dict()
        self.GADformula = list()

    # 如果操作符左右两边都是数字则返回 True
    def isdigit(self, fomula):
        # print("fomula.expr1: ", fomula.expr1)
        # print("fomula.expr2: ", fomula.expr2)
        assert isinstance(fomula, murphi.OpExpr)
        if isinstance(fomula.expr1, murphi.OpExpr):
            if self.isdigit(fomula.expr1) == False:
                return False
        if isinstance(fomula.expr2, murphi.OpExpr):
            if self.isdigit(fomula.expr2) == False:
                return False
        if isinstance(fomula.expr1, murphi.VarExpr) and (fomula.expr1.name).isdigit() and isinstance(fomula.expr2,
                                                                                                     murphi.VarExpr) and (
                fomula.expr2.name).isdigit():
            return True
        else:
            return False
        
    # 对 murphi 中的 val 转换为 str，如果是数字，则转为 int
    def getVal(self, expr):
        if isinstance(expr, murphi.EnumValExpr):
            return str(expr.enum_val)
        elif isinstance(expr, murphi.BooleanExpr):
            return True if expr.val else False
        elif str(expr).isdigit():
            return int(str(expr))
        else:
            return str(expr)
    
    # 将 murphi 中获取的公式的操作符转换为 smt 公式的操作符返回
    def smtOP(self, expr1, expr2, op):
        global EnumType_vars
        if op == '=':
            if str(expr1) in EnumType_vars and str(expr2) in enum_value_map[EnumType_vars[str(expr1)]]:
                return expr1 == enum_value_map[EnumType_vars[str(expr1)]][expr2]
            return expr1 == expr2
        if op == '!=':
            if str(expr1) in EnumType_vars and str(expr2) in enum_value_map[EnumType_vars[str(expr1)]]:
                return expr1 != enum_value_map[EnumType_vars[str(expr1)]][expr2]
            return expr1 != expr2
        if op == '&':
            return And(expr1, expr2)
        if op == '|':
            return Or(expr1, expr2)
        if op == '->':
            return Implies(expr1, expr2)
        
    # 判断公式两边是否相等
    def digitfomulaResult(self,digitf):
        assert isinstance(digitf, murphi.OpExpr)
        op1 = digitf.expr1
        op2 = digitf.expr2

        digitseq = op1==op2

        if digitf.op in ('='):
            return digitseq
        elif digitf.op in ('!='):
            return not digitseq

    # 对从 murphi 中获取的 inv 进行 smt 处理
    def getVars(self, fomula, vardict, statements, replacement="", assign_var_dict = dict()):
        if replacement:
            match = re.search(r'@(\d+)', replacement)
            match_int = int(match.group(1))
        # print("fomula: ", fomula)   # !(n[2] = E) & !(n[1] = E) & !(n[2] = C) & !(n[1] = C) & !(n[2] = T & x = true) & !(n[1] = T & x = true) & !(n[2] = I) & !(n[1] = I)
        global EnumType_vars    # {'n[1]': 'state', "n[1]'": 'state', 'n[2]': 'state', "n[2]'": 'state'}
        global all_vars
        # for guard and inv
        # print("statements: ", statements)    # [n[1] == I, n[1]' == T, n[2] == n[2]', x == x']
        # print("vardict: ", vardict)    # {'n[1]': [n[1], ArrayIndex(VarExpr('n'), VarExpr('1'))], "n[1]'": [n[1]'], 'n[2]': [n[2], ArrayIndex(VarExpr('n'), VarExpr('2'))], "n[2]'": [n[2]'], 'x': [x, VarExpr('x')], "x'": [x']}
        if isinstance(fomula, murphi.OpExpr):
            if self.isdigit(fomula):
                statements.append(self.digitfomulaResult(fomula))
            else:
                if isinstance(fomula.expr1, murphi.OpExpr) or isinstance(fomula.expr1, murphi.NegExpr) or isinstance(
                        fomula.expr2, murphi.OpExpr) or isinstance(fomula.expr2, murphi.NegExpr):
                    newlist1 = []
                    newlist2 = []
                    if isinstance(fomula.expr1, murphi.OpExpr) or isinstance(fomula.expr1, murphi.NegExpr):
                        _, newlist1 = self.getVars(fomula.expr1, vardict, newlist1, replacement, assign_var_dict)
                    if isinstance(fomula.expr2, murphi.OpExpr) or isinstance(fomula.expr2, murphi.NegExpr):
                        _, newlist2 = self.getVars(fomula.expr2, vardict, newlist2, replacement, assign_var_dict)
                    if len(newlist1) and len(newlist2):

                        statements.append(self.smtOP(newlist1[0], newlist2[0], fomula.op))
                    elif len(newlist2):
                        statements.append(newlist2[0])
                    elif len(newlist1):
                        statements.append(newlist1[0])
                else:
                    # print("fomula: ", fomula)
                    if str(fomula.expr1) in assign_var_dict:
                        replacement = f"@{match_int+1}"
                    else:
                        replacement = f"@{match_int}"
                    if isinstance(fomula.expr2, murphi.EnumValExpr) or isinstance(fomula.expr2, murphi.BooleanExpr) or (
                            isinstance(fomula.expr2, murphi.VarExpr) and fomula.expr2.name.isdigit()):
                        if str(fomula.expr1) + replacement not in vardict.keys():
                            vardict[str(fomula.expr1) + replacement] = all_vars[str(fomula.expr1) + replacement]
                            if str(fomula.expr1) in self.scalarsetVars and str(
                                    fomula.expr1) + replacement not in self.dataVars:
                                self.dataVars.append(str(fomula.expr1) + replacement)
                        val = self.getVal(fomula.expr2)
                        statements.append(self.smtOP(all_vars[str(fomula.expr1) + replacement][0], val, fomula.op))
                    else:
                        # print("str(fomula.expr1): ", fomula, str(fomula.expr1), type(fomula.expr1))
                        if (isinstance(fomula.expr1, murphi.VarExpr) and fomula.expr1.name.isdigit()):
                            # print(fomula.expr1.name, fomula.expr1.typ)
                            replacement1 = ""
                            all_vars[str(fomula.expr1) + replacement1] = setKey(fomula.expr1, '', isbool=isinstance(fomula.expr1.typ, murphi.BooleanType),
                                            isdigit=fomula.expr1.name.isdigit() or isinstance(fomula.expr1.typ,murphi.RngType),
                                            isenum=isinstance(fomula.expr1.typ, murphi.EnumType))
                        else:
                            replacement1 = f"@{match_int}"
                            if str(fomula.expr1) + replacement1 not in vardict.keys():
                                vardict[str(fomula.expr1) + replacement1] = all_vars[str(fomula.expr1) + replacement1]
                                if str(fomula.expr1) in self.scalarsetVars and str(
                                        fomula.expr1) + replacement1 not in self.dataVars:
                                    self.dataVars.append(str(fomula.expr1) + replacement1)
                        
                        if (isinstance(fomula.expr2, murphi.VarExpr) and fomula.expr2.name.isdigit()):
                            replacement2 = ""
                        else:
                            replacement2 = f"@{match_int}"
                            if str(fomula.expr2) + replacement2 not in vardict.keys():
                                vardict[str(fomula.expr2) + replacement2] = all_vars[str(fomula.expr2) + replacement2]
                                if str(fomula.expr2) in self.scalarsetVars and str(
                                        fomula.expr2) + replacement2 not in self.dataVars:
                                    self.dataVars.append(str(fomula.expr2) + replacement2)
            
                        statements.append(self.smtOP(all_vars[str(fomula.expr1) + replacement1][0],
                                                     all_vars[str(fomula.expr2) + replacement2][0], fomula.op))

        # for assignment
        if isinstance(fomula, murphi.AssignCmd):
            if isinstance(fomula.expr, murphi.EnumValExpr) or isinstance(fomula.expr, murphi.BooleanExpr) or (
                    isinstance(fomula.expr, murphi.VarExpr) and fomula.expr.name.isdigit()):
                if str(fomula.var) + replacement not in vardict.keys():
                    vardict[str(fomula.var) + replacement] = all_vars[str(fomula.var) + replacement]
                    if str(fomula.var) in self.scalarsetVars and str(fomula.var) + replacement not in self.dataVars:
                        self.dataVars.append(str(fomula.var) + replacement)

                val = self.getVal(fomula.expr)
                statements.append(self.smtOP(all_vars[str(fomula.var) + replacement][0], val, '='))
            else:
                if replacement:
                    expr_replacement = f'@{match_int-1}'
                if str(fomula.var) + replacement not in vardict.keys():
                    vardict[str(fomula.var) + replacement] = all_vars[str(fomula.var) + replacement]
                    if str(fomula.var) in self.scalarsetVars and str(fomula.var) + replacement not in self.dataVars:
                        self.dataVars.append(str(fomula.var) + replacement)
                if str(fomula.expr) + expr_replacement not in vardict.keys():
                    vardict[str(fomula.expr) + expr_replacement] = all_vars[str(fomula.expr) + expr_replacement]
                    if str(fomula.expr) in self.scalarsetVars and str(
                            fomula.expr) + expr_replacement not in self.dataVars:
                        self.dataVars.append(str(fomula.expr) + expr_replacement)
                statements.append(self.smtOP(all_vars[str(fomula.var) + replacement][0],
                                             all_vars[str(fomula.expr) + expr_replacement][0], '='))

        # for negInv
        if isinstance(fomula, murphi.NegExpr):
            # assert isinstance(fomula.expr, murphi.OpExpr)
            if isinstance(fomula.expr, murphi.NegExpr):
                self.getVars(fomula.expr.expr, vardict, statements, replacement, assign_var_dict)
            else:
                if fomula.expr.op == '->':
                    # to cnf
                    cnf = murphi.OpExpr('&', fomula.expr.expr1, murphi.NegExpr(fomula.expr.expr2))
                    self.getVars(cnf, vardict, statements, replacement, assign_var_dict)
                if fomula.expr.op == '=':
                    neq = murphi.OpExpr('!=', fomula.expr.expr1, fomula.expr.expr2)

                    self.getVars(neq, vardict, statements, replacement, assign_var_dict)
                if fomula.expr.op == '!=':
                    self.getVars(murphi.OpExpr('=', fomula.expr.expr1, fomula.expr.expr2), vardict, statements,
                                 replacement, assign_var_dict)
                if fomula.expr.op == '&':
                    impl = murphi.OpExpr('->', fomula.expr.expr1, murphi.NegExpr(fomula.expr.expr2))
                    self.getVars(impl, vardict, statements, replacement, assign_var_dict)
                if fomula.expr.op == '|':
                    cnf = murphi.OpExpr('&', murphi.NegExpr(fomula.expr.expr1), murphi.NegExpr(fomula.expr.expr2))

                    self.getVars(cnf, vardict, statements, replacement, assign_var_dict)
        return vardict, statements
    
    def merge_split_lists(self, input_list, chunk_size):
        # print(input_list, chunk_size)
        if len(input_list) == 1:
            return input_list
        elif chunk_size == 1:
            return input_list
        else:
            merge_list = [join_z3_statements(input_list[i:i + chunk_size]) for i in range(0, len(input_list), chunk_size)]
            return merge_list
    
    def get_var_type(self, var):
        if isinstance(var, murphi.FieldName):
            type = self.get_var_type(var.v)
        if isinstance(var, murphi.ArrayIndex):
            type = self.get_var_type(var.idx)
        if isinstance(var, murphi.VarExpr):
            type = var.typ
        return type

    def murphi_paraInv(self, inv):
        inv = str(inv)
        inv_str = ""
        subdict = {}
        noteqVars = []
        self.Invvar, self.Invformula = self.getVars(self.Inv, self.Invvar, self.Invformula, '', {})
        for var, lst in self.Invvar.items():
            pattern = r'\[(\d+)\]'
            para_num = re.findall(pattern, var)[0]
            replacement = chr(ord('i') + int(para_num) - 1)
            typ = self.get_var_type(lst[1])
            if replacement not in noteqVars:
                inv_str = inv_str + murphi.indent(f"forall {replacement} : {typ} do\n", 2)
                noteqVars.append(replacement)
            # subdict[var] = var.replace(para_num, chr(ord('i') + int(para_num) - 1))
            subdict[var] = re.sub(pattern, lambda match: f'[{replacement}]', var)

        if len(noteqVars) == 2:
            inv_str = inv_str + f"{noteqVars[0]} != {noteqVars[1]} -> \n"

        for arg_var, para_var in subdict.items():
            inv = murphi.indent(inv.replace(arg_var, para_var), 2)
        inv_str = inv_str + inv + "\n"

        for idx in range(len(noteqVars)):
            inv_str = inv_str + "end" + murphi.indent("", 2)
        inv_str = inv_str + ";"

        # print("inv_str:\n", inv_str)
        return inv_str
    
    def get_transition(self, upper_bound):
        s_transition = time.time()

        # print("self.init_state: ", self.init_state)
        # self.initvar, self.initformula = self.getVars(self.init_state, self.initvar, self.initformula, f'@{0}', {})
        # print("initvar: ", self.initvar)
        # print("initfomula: ", self.initformula)

        for k in range(0, upper_bound-1):
            # for guard's variables
            self.guardvar, self.guardformula = self.getVars(self.guard, self.guardvar, self.guardformula, f'@{k}', {})

        assign_var = dict()

        for k in range(1, upper_bound):
            # for assign's variables
            for assign in self.assign:
                if isinstance(assign, murphi.AssignCmd):
                    assign_var[str(assign.var)] = assign.var
                    if k > 0:
                        self.assignvar, self.assignformula = self.getVars(assign, self.assignvar, self.assignformula, f'@{k}', {})
                elif isinstance(assign, murphi.IfCmd):

                    if_cond = []
                    else_cond = []
                    if k > 0:
                        self.assignvar, if_cond = self.getVars(assign.if_branches[0][0], self.assignvar, if_cond, f'@{k-1}', assign_var)
                        self.assignvar, else_cond = self.getVars(murphi.NegExpr(assign.if_branches[0][0]), self.assignvar,
                                                            else_cond, f'@{k-1}', assign_var)

                    if_assign = []
                    if_variables = []
                    for if_as in assign.if_branches[0][1]:
                        self.assignvar, if_assign = self.getVars(if_as, self.assignvar, if_assign, f'@{k}', {})
                        assert isinstance(if_as, murphi.AssignCmd)
                        if_variables.append(if_as.var)

                    else_assign = []
                    else_variables = []
                    if assign.else_branch:
                        for else_as in assign.else_branch:
                            self.assignvar, else_assign = self.getVars(else_as, self.assignvar, else_assign, f'@{k}', {})
                            assert isinstance(else_as, murphi.AssignCmd)
                            else_variables.append(else_as.var)

                    

                    # fix: how to handle when "else" not occure?
                    # fix: assumptions when variables different from if_branch & else_branch
                    if else_assign:
                        if_variables_bounds = []
                        else_variables_bounds = []
                        if_assumptions = [elem for elem in else_variables if elem not in if_variables]
                        else_assumptions = [elem for elem in if_variables if elem not in else_variables]

                        if k > 0:
                            for if_assumption in if_assumptions:
                                if_variables_bounds.append(
                                    self.smtOP(all_vars[str(if_assumption) + f'@{k}'][0], all_vars[str(if_assumption) + f'@{k-1}'][0], '='))
                            
                            for else_assumption in else_assumptions:
                                else_variables_bounds.append(
                                    self.smtOP(all_vars[str(else_assumption) + f'@{k}'][0], all_vars[str(else_assumption) + f'@{k-1}'][0], '='))

                        self.assignformula.append(Or(join_z3_statements(if_cond + if_assign + if_variables_bounds),
                                                join_z3_statements(else_cond + else_assign + else_variables_bounds)))
                    else:
                        else_variables_bounds = []
                        if k > 0:
                            for variables in if_variables:
                                else_variables_bounds.append(
                                    self.smtOP(all_vars[str(variables) + f'@{k}'][0], all_vars[str(variables) + f'@{k-1}'][0], '='))

                        self.assignformula.append(Or(join_z3_statements(if_cond + if_assign),
                                                join_z3_statements(else_cond + else_variables_bounds)))
        
        for k in range(0, upper_bound):
            # for assumption's variables
            for assumption in self.assumption:
                if str(assumption) + f'@{k}' not in self.assumptionvar.keys():
                    self.assumptionvar[str(assumption) + f'@{k}'] = all_vars[str(assumption) + f'@{k}']
                    if str(assumption) + f'@{k}' not in self.dataVars:
                        self.dataVars.append(str(assumption) + f'@{k}')

                if k + 1 < upper_bound:
                    self.assumptionformula.append(
                        self.smtOP(all_vars[str(assumption) + f'@{k+1}'][0], all_vars[str(assumption) + f'@{k}'][0], '='))
            
            # self.negInvvar, self.negInvformula = self.getVars(self.negInv, self.negInvvar, self.negInvformula, f'@{k}', {})

            for axiom_sub in self.axiom_ins:
                self.axiomvar, self.axiomformula = self.getVars(axiom_sub, self.axiomvar, self.axiomformula, f'@{k}', {})

        guard_mod = len(self.guardformula)/(upper_bound-1)
        assign_mod = len(self.assignformula)/(upper_bound-1)
        assumption_mod = len(self.assumptionformula)/(upper_bound-1)

        guard_formula = list()
        assign_formula = list()
        assumption_formula = list()
        if self.guardformula:
            guard_formula = self.merge_split_lists(self.guardformula, int(guard_mod))
        else:
            for k in range(0, upper_bound-1):
                guard_formula.append(True) 
        if self.assignformula:
            assign_formula = self.merge_split_lists(self.assignformula, int(assign_mod))
        else:
            for k in range(0, upper_bound):
                assign_formula.append(True)
        if self.assumptionformula:
            assumption_formula = self.merge_split_lists(self.assumptionformula, int(assumption_mod))
        else:
            for k in range(0, upper_bound):
                assumption_formula.append(True)

        # init_formula = self.initformula
        # negInv_formula = self.negInvformula
        axiom_formula = self.axiomformula

        
        # print("guardvar: ", self.guardvar)
        # print("guardformula: ", self.guardformula)
        
        # print("assignvar: ", self.assignvar)
        # print("assignformula: ", self.assignformula)

        # print("assumptionvar: ", self.assumptionvar)
        # print("assumptionformula: ", self.assumptionformula)
        
        # print("negInvvar: ", self.negInvvar)
        # print("negInvformula: ", self.negInvformula)

        # print("axiomvar: ", self.axiomvar)
        # print("axiomformula: ", self.axiomformula)
        return guard_formula, assign_formula, assumption_formula, axiom_formula
    
    def get_init_guard(self):
        # print("init: ", self.init_state)
        # print("guard: ", self.guard)
        init_and_guard = None
        init_old = copy.deepcopy(self.init_state)
        guard_old = copy.deepcopy(self.guard)
        guard_list = list()
        guard_list = self.split_formula(guard_old, guard_list)
        # print("guard_list: ", guard_list)
        init_new = self.guard_replace_init(init_old, guard_list, [])
        init_new = self.guard_replace_init(init_new, guard_list, [])
        # print("init_old: ", init_old)
        # print("init_new: ", init_new)
        init_and_guard = murphi.OpExpr("&", init_new, guard_old)
        # print("init_and_guard: ", init_and_guard)
        self.GADvar, self.GADformula = self.getVars(init_and_guard, self.GADvar, self.GADformula, f'@{0}', {})
        GAD_formula = self.GADformula
        return GAD_formula
    
    def guard_replace_init(self, init_equal, guard_list, exist_list):
        init_new = None
        if isinstance(init_equal, murphi.OpExpr):
            if init_equal.op == "=" or init_equal.op == "!=":
                for guard in guard_list:
                    if isinstance(guard, murphi.OpExpr):
                        if guard.expr1 == init_equal.expr1:
                            # print(guard.expr1, init_equal.expr1, init_equal)
                            # print("exist_list: ", exist_list)
                            exist_list.append(init_equal)
                            init_new = murphi.BooleanExpr(True)
                        else:
                            if init_equal in exist_list:
                                init_new = murphi.BooleanExpr(True)
                            else:
                                init_new = init_equal
                    else:
                        if init_equal in exist_list:
                            init_new = murphi.BooleanExpr(True)
                        else:
                            init_new = init_equal
                # print("init_new: ", init_new)
            else:
                # print("init_equal: ", init_equal)
                # print("result: ", self.guard_replace_init(init_equal.expr1, guard_list, exist_list), self.guard_replace_init(init_equal.expr2, guard_list, exist_list))
                if self.guard_replace_init(init_equal.expr1, guard_list, exist_list) == murphi.BooleanExpr(True) and self.guard_replace_init(init_equal.expr2, guard_list, exist_list) == murphi.BooleanExpr(True):
                    init_new = murphi.BooleanExpr(True)
                else:
                    if self.guard_replace_init(init_equal.expr1, guard_list, exist_list) == murphi.BooleanExpr(True):
                        init_new = init_equal.expr2
                    elif self.guard_replace_init(init_equal.expr2, guard_list, exist_list) == murphi.BooleanExpr(True):
                        init_new = init_equal.expr1
                    else:
                        if self.guard_replace_init(init_equal.expr1, guard_list, exist_list) in exist_list and (self.guard_replace_init(init_equal.expr2, guard_list, exist_list) in exist_list):
                            init_new = murphi.BooleanExpr(True)
                        else:
                            if self.guard_replace_init(init_equal.expr1, guard_list, exist_list) in exist_list:
                                init_new = self.guard_replace_init(init_equal.expr2, guard_list, exist_list) in exist_list
                            elif self.guard_replace_init(init_equal.expr2, guard_list, exist_list) in exist_list:
                                init_new = self.guard_replace_init(init_equal.expr1, guard_list, exist_list)
                            else:
                                init_new = murphi.OpExpr(init_equal.op, self.guard_replace_init(init_equal.expr1, guard_list, exist_list), self.guard_replace_init(init_equal.expr2, guard_list, exist_list))
                    
                # print("init_new: ", init_new)
        elif isinstance(init_equal, murphi.NegExpr):
            init_new = murphi.NegExpr(self.guard_replace_init(init_equal.expr, guard_list, exist_list))
        else:
            init_new = init_equal
        return init_new

    def split_formula(self, formula, formula_list):
        if isinstance(formula, murphi.OpExpr):
            if formula.op == "=" or formula.op == "!=":
                formula_list.append(formula)
            else:
                formula_list = self.split_formula(formula.expr1, formula_list)
                formula_list = self.split_formula(formula.expr2, formula_list)
        elif isinstance(formula, murphi.NegExpr):
            formula_list = self.split_formula(formula.expr)
        else:
            formula_list.append(formula)
        
        return formula_list
    
    def get_Init_LTL(self):
        self.initvar, self.initformula = self.getVars(self.init_state, self.initvar, self.initformula, f'@{0}', {})
        
        init_formula = self.initformula
        return init_formula

    def get_Inv_LTL(self, upper_bound):
        for k in range(upper_bound):
            self.negInvvar, self.negInvformula = self.getVars(self.negInv, self.negInvvar, self.negInvformula, f'@{k}', {})

        negInv_formula = self.negInvformula

        # print("negInvvar: ", self.negInvvar)
        # print("negInvformula: ", self.negInvformula)
        return negInv_formula

def smt_bmc(solver, init_f, negInv_f, axiom_f, formula_dict, bound):
    s_add_time = time.time()
    bmc_solver = solver

    formula_list = list()

    if bound == 0:
        bmc_solver.add(init_f[bound])

    if bound > 0:
        bmc_solver.add(formula_dict[f'@{bound-1}'])

    bmc_tmp_solver = Solver()
    
    bmc_tmp_solver.add(bmc_solver.assertions())
    bmc_tmp_solver.add(negInv_f[bound])
    if axiom_f:
        bmc_tmp_solver.add(axiom_f[bound])

    e_add_time = time.time()
    a_add_time = e_add_time - s_add_time
    # print(f"the {bound} add time is {a_add_time:.6f}")

    bmc_bound = bound
    # print("bmc_solver: ", bmc_solver, bound, procount)
    # print(bmc_solver.check())
    s_sat_time = time.time()
    if bmc_tmp_solver.check() == sat:
        model = bmc_tmp_solver.model()
        # print(model)
        bmc_is_sat = True
    else:
        bmc_is_sat = False
    e_sat_time = time.time()
    a_sat_time = e_sat_time - s_sat_time
    # print(f"the {bound} sat time is {a_sat_time:.6f}")
    return bmc_is_sat, bmc_bound, bmc_solver

def mul_smt_bmc(solver, init_f, negInv_f, axiom_f, formula_dict, bound, procount):
    bmc_solver = solver

    formula_list = list()

    if bound == procount:
        bmc_solver.add(init_f[0])
        for pro in range(procount):
            bmc_solver.add(formula_dict[f'@{pro}'])

    if bound > procount:
        bmc_solver.add(formula_dict[f'@{bound-1}'])

    bmc_tmp_solver = Solver()
    bmc_tmp_solver.add(bmc_solver.assertions())
    bmc_tmp_solver.add(negInv_f[bound])
    if axiom_f:
        bmc_tmp_solver.add(axiom_f[bound])
    # smt_formula = join_z3_statements(formula_list)
    # bmc_solver.add(smt_formula)

    bmc_bound = bound
    # print("bmc_tmp_solver: ", bmc_tmp_solver, bound, procount)
    # print(bmc_solver.check())
        
    if bmc_tmp_solver.check() == sat:
        model = bmc_tmp_solver.model()
        # print(model)
        bmc_is_sat = True
    else:
        bmc_is_sat = False
    return bmc_is_sat, bmc_bound, bmc_solver

def smt_bmc_guard(solver, init_f, negInv_f, axiom_f, formula_dict, bound):
    bmc_solver = solver

    formula_list = list()

    if bound == 0:
        bmc_solver.add(init_f[0])

    if bound > 0:
        bmc_solver.add(formula_dict[f'@{bound-1}'])

    bmc_tmp_solver = Solver()
    bmc_tmp_solver.add(bmc_solver.assertions())
    bmc_tmp_solver.add(negInv_f[bound])
    if axiom_f:
        bmc_tmp_solver.add(axiom_f[bound])
    # smt_formula = join_z3_statements(formula_list)
    # bmc_solver.add(smt_formula)

    bmc_bound = bound
    # print("bmc_solver: ", bmc_solver, bound)
    # print(bmc_solver.check())
    
    negGuard_model = None
    if bmc_tmp_solver.check() == sat:
        negGuard_model = bmc_tmp_solver.model()
        # print("model: ",negGuard_model)
        bmc_is_sat = True
    else:
        bmc_is_sat = False
    return bmc_is_sat, bmc_bound, bmc_solver, negGuard_model


def write_murphi(s_path, p_path, str):
    global inv_count
    path_name = p_path + f'_{inv_count}.m'
    with open(s_path + ".m", "r") as input_file:
        with open(path_name, "a") as output_file:
            i_str = input_file.read()
            output_file.write(i_str)
            output_file.write("\n")
            output_file.write(str)
            output_file.write("\n")
    return path_name

def dedoubleNeg(fomula):
        if isinstance(fomula, murphi.NegExpr) and isinstance(fomula.expr, murphi.NegExpr):
            return fomula.expr.expr
        else:
            return fomula

def get_Var_LTL(specific_var, ScalarSetType_vars, BooleanType_vars, c_all_ins_vars, upper_bound):
    for k in range(upper_bound):
        for var, typ in specific_var.items():
            if isinstance(typ, murphi.ScalarSetType) or isinstance(typ, murphi.RngType):
                if var not in ScalarSetType_vars:
                    ScalarSetType_vars.append(var)
            elif isinstance(typ, murphi.BooleanType):
                if var + f'@{k}' not in BooleanType_vars:
                    BooleanType_vars.append(var + f'@{k}')
                # BooleanType_vars.append(var)
            elif isinstance(typ, murphi.EnumType):
                if str(var) in murphi.specific_enum_var.keys():
                    EnumType_vars[str(var) + f'@{k}'] = murphi.specific_enum_var[str(var)]
                    # EnumType_vars[str(var)] = murphi.specific_enum_var[str(var)]

    # print("ScalarSetType_vars: ", ScalarSetType_vars)
    # print("BooleanType_vars: ", BooleanType_vars)
    # print("EnumType_vars: ", EnumType_vars)

    # print("all_ins_vars: ", all_ins_vars)
    for k in range(upper_bound):
        for var, typ in specific_var.items():
            if var in c_all_ins_vars.keys():
                # if var not in all_vars:
                #     all_vars[var] = setKey(c.all_ins_vars[var], '', isbool=isinstance(typ, murphi.BooleanType),
                #                 isdigit=isinstance(typ, murphi.ScalarSetType),
                #                 isenum=isinstance(typ, murphi.EnumType))
                if var + f'@{k}' not in all_vars:
                    all_vars[var + f'@{k}'] = setKey(c_all_ins_vars[var], f'@{k}', isbool=isinstance(typ, murphi.BooleanType),
                                            isdigit=isinstance(typ, murphi.ScalarSetType) or isinstance(typ,murphi.RngType),
                                            isenum=isinstance(typ, murphi.EnumType))
                    if var not in all_ins_vars:
                        all_ins_vars.append(var)
                    if var + f'@{k}' not in all_LTL_vars:
                        all_LTL_vars.append(var + f'@{k}')
    
    # print("all_vars: ", all_vars)
    # print("all_ins_vars: ",all_ins_vars)
    # print("all_LTL_vars: ", all_LTL_vars)
    return ScalarSetType_vars, BooleanType_vars
                        

def get_BMC_formula(lower_procount, upper_procount, upper_bound, inv_path):
    protocol_name = inv_path.split("/")[-1]

    s_constructF = time.time()
    c = constructSMT.GetSMTformula(protocol_name, parse_name=inv_path, dl_inv=None)
    c.getInit()
    c.get_Axiom()
    c.getInv_2()
    # c.getInvs() 
    e_constructF = time.time()
    t_constructF = e_constructF - s_constructF

    # bmc_check_inv = c.invariant_ins[f'{protocol_name}']

    init = c.init_instance

    axiom = c.axiom_instance

    defEnum(c)

    specific_var = murphi.specific_var  # get all vars in protocol
    ScalarSetType_vars = []
    BooleanType_vars = []

    # print("specific_var: ", specific_var)
    c_all_ins_vars = c.all_ins_vars
    # print("c_all_ins_vars: ", c_all_ins_vars)

    ScalarSetType_vars, BooleanType_vars = get_Var_LTL(specific_var, ScalarSetType_vars, BooleanType_vars, c_all_ins_vars, upper_bound)

    # check_ori_inv = inv

    all_LTL_formula = dict()

    # formula_instances 存储的是所有实例化后的 guard assign assumption 以及 !inv
    # print("c.formula_instances: ", c.formula_instances)

    init_formula = list()
    axiom_formula = list()
    GAD_LTL_formula = list()
    all_LTL_formula = dict()
    # assign_formula, assumption_formula, axiom_formula
    bmc_fomula_start = time.time()
    rule_count = 0
    for name, instance in c.formula_instances.items():
        rule_count += 1
        sub_LTL_formula = dict()

        bmc_check_inv = dedoubleNeg(murphi.NegExpr(instance["!inv"]))
        # print("bmc_check_inv: ", bmc_check_inv)
        current_procotol = name.split("_")[0]
        current_rule = "_".join(name.split("_")[1:])
        BMCLF = BMC_LTL_Formula(protocol_name, BooleanType_vars, c.enum_typ_map, c.typ_map, ScalarSetType_vars,
                                upper_bound, lower_procount, upper_procount, name, init, axiom, instance, inv_path, bmc_inv = bmc_check_inv)
        
        guard_formula, assign_formula, assumption_formula, axiom_formula = BMCLF.get_transition(upper_bound)
        # GAD_formula = BMCLF.get_init_guard()
        # GAD_LTL_formula.extend(GAD_formula)
        GAD_LTL_formula.append(murphi.NegExpr(instance["guard"]))
        
        if rule_count == len(c.formula_instances):
            init_formula = BMCLF.get_Init_LTL()
            # print("init_formula: ", init_formula)
            # print("GAD_LTL_formula: ", GAD_LTL_formula)
        # print("GAD_formula: ", GAD_formula)
    
        # print("-----------------------------------------------------------------------------------")
        # print("current_rule: ", current_rule)
        # print("guard_formula: ", guard_formula)
        # print("assign_formula: ", assign_formula)
        # print("assumption_formula: ", assumption_formula)
        # print("axiom_formula: ", axiom_formula)
        # print("-----------------------------------------------------------------------------------")
        for k in range(upper_bound-1):
            sub_LTL_list = list()
            sub_LTL_list.append(guard_formula[k])
            sub_LTL_list.append(assign_formula[k])
            sub_LTL_list.append(assumption_formula[k])
            sub_LTL_formula[f'@{k}'] = join_z3_statements(sub_LTL_list)
        all_LTL_formula[current_rule] = sub_LTL_formula
    
    # print("all_LTL_formula: ", all_LTL_formula)
    LTL_formula_tmp = dict()
    for rule_name, rule_dict in all_LTL_formula.items():
        # print("rule: ", rule_name, rule_dict)
        for ltl, ltl_formula in rule_dict.items():
            if ltl not in LTL_formula_tmp:
                LTL_formula_tmp[ltl] = list()
                LTL_formula_tmp[ltl].append(ltl_formula)
            else:
                LTL_formula_tmp[ltl].append(ltl_formula)
    
    for ltl_con, ltl_for in LTL_formula_tmp.items():
        LTL_formula_tmp[ltl_con] = disjoin_z3_statements(ltl_for)
    # print("LTL_formula_tmp: ", LTL_formula_tmp)
    all_LTL_formula = LTL_formula_tmp

    bmc_fomula_end = time.time()
    global bmc_fomula_time
    bmc_fomula_time = bmc_fomula_end - bmc_fomula_start

    # global str_murphi
    # str_murphi = SMVLF.murphi_paraInv(bmc_check_inv)

    return init_formula, axiom_formula, all_LTL_formula, ScalarSetType_vars, BooleanType_vars, GAD_LTL_formula

def get_Inv_formula(upper_bound, inv, inv_path, ScalarSetType_vars, BooleanType_vars):
    protocol_name = inv_path.split("/")[-1]

    c = constructSMT.GetSMTformula(protocol_name, parse_name=inv_path, dl_inv=inv)
    c.getInit()
    c.get_Axiom()
    c.get_str_Inv()
    # c.getInvs() 

    bmc_check_inv = murphi.NegExpr(c.invariant_ins[f'{protocol_name}'])

    BMCLF = BMC_LTL_Formula(protocol_name, BooleanType_vars, c.enum_typ_map, c.typ_map, ScalarSetType_vars,
                                upper_bound, lower_procount = 0, upper_procount = 0, name = None, init_state = {}, axiom_ins = {}, instance = {}, inv_path = None, bmc_inv =  bmc_check_inv)
    negInv_formula = BMCLF.get_Inv_LTL(upper_bound)
    # print("negInv_formula: ", negInv_formula)

    bmc_check_inv = murphi.NegExpr(dedoubleNeg(bmc_check_inv))

    return bmc_check_inv, negInv_formula



def call_BMC(init_fomula, axiom_formula, all_LTL_formula, upper_bound, inv, mfile_path, ScalarSetType_vars, BooleanType_vars):
    bmc_check_inv, negInv_formula = get_Inv_formula(upper_bound, inv, mfile_path, ScalarSetType_vars, BooleanType_vars)
    bmc_check_start = time.time()
    check_result = True
    solver = Solver()
    for bound in range(0, upper_bound):
        if bound == 0:
            bmc_sat, bmc_bound, bmc_solver = smt_bmc(solver, init_fomula, negInv_formula, axiom_formula, all_LTL_formula, bound)
        else:
            bmc_sat, bmc_bound, bmc_solver = smt_bmc(bmc_solver, init_fomula, negInv_formula, axiom_formula, all_LTL_formula, bound)
        # print("bmc_sat: ", bmc_sat)
        # print("bmc_bound: ", bmc_bound)
        if bmc_sat:
            # print("bmc_sat: ", bmc_sat)
            print("found cex in bound ", bmc_bound)
            check_result = False
            break
        else:
            # print("bmc_sat: ", bmc_sat)
            # print("not found cex in bound ", bmc_bound)
            check_result = True
    bmc_check_end = time.time()
    global bmc_check_time
    bmc_check_time = bmc_check_end - bmc_check_start
    print(f"bmc_check_time {bmc_check_time:.6f}")
    return check_result, bmc_check_inv

def mul_call_BMC(init_fomula, axiom_formula, all_LTL_formula, upper_bound, inv, mfile_path, ScalarSetType_vars, BooleanType_vars, procount):
    bmc_check_inv, negInv_formula = get_Inv_formula(upper_bound, inv, mfile_path, ScalarSetType_vars, BooleanType_vars)
    bmc_check_start = time.time()
    check_result = True
    solver = Solver()
    for bound in range(procount, upper_bound):
        # print("bound: ", bound, procount)
        if bound == procount:
            bmc_sat, bmc_bound, bmc_solver = mul_smt_bmc(solver, init_fomula, negInv_formula, axiom_formula, all_LTL_formula, bound, procount)
        else:
            bmc_sat, bmc_bound, bmc_solver = mul_smt_bmc(bmc_solver, init_fomula, negInv_formula, axiom_formula, all_LTL_formula, bound, procount)
        # print("bmc_sat: ", bmc_sat)
        # print("bmc_bound: ", bmc_bound)
        if bmc_sat:
            # print("bmc_sat: ", bmc_sat)
            print(f"process_id {procount} found cex in bound ", bmc_bound)
            check_result = False
            break
        else:
            # print("bmc_sat: ", bmc_sat)
            # print("not found cex in bound ", bmc_bound)
            check_result = True
    bmc_check_end = time.time()
    global bmc_check_time
    bmc_check_time = bmc_check_end - bmc_check_start
    return check_result, bmc_check_inv

def call_BMC_guard(init_fomula, axiom_formula, all_LTL_formula, upper_bound, neg_guard, mfile_path, ScalarSetType_vars, BooleanType_vars):
    bmc_check_negGuard, negGuard_formula = get_Inv_formula(upper_bound, neg_guard, mfile_path, ScalarSetType_vars, BooleanType_vars)
    bmc_check_start = time.time()
    check_result = True
    guard_result = True
    init_solver = Solver()
    for bound in range(0, upper_bound):
        if bound == 0:
            negGuard_sat, negGuard_bound, negGuard_solver, negGuard_model = smt_bmc_guard(init_solver, init_fomula, negGuard_formula, axiom_formula, all_LTL_formula, bound)
        else:
            negGuard_sat, negGuard_bound, negGuard_solver, negGuard_model = smt_bmc_guard(negGuard_solver, init_fomula, negGuard_formula, axiom_formula, all_LTL_formula, bound)
        # print("bmc_sat: ", bmc_sat)
        # print("bmc_bound: ", bmc_bound)
        if negGuard_sat:
            # print("bmc_sat: ", bmc_sat)
            # print("found negGuard's solution in bound ", negGuard_bound)
            guard_result = False
            break
        else:
            # print("bmc_sat: ", bmc_sat)
            # print("not found cex in bound ", bmc_bound)
            guard_result = True
            
    # print("all_vars: ", all_vars)
    all_model = list()
    new_init_formula = list()
    # print("negGuard_model: ", negGuard_model, len(negGuard_model))
    if negGuard_model:
        for m in range(len(negGuard_model)):
            if f"@{bound}" in str(negGuard_model[m]):
                new_model = model_trans(negGuard_model[m], negGuard_model[negGuard_model[m]], negGuard_bound)
                # print("new_model: ", new_model)
                all_model.extend(new_model)
        new_init_formula.append(join_z3_statements(all_model))
    # print("new startstate is ", new_init_formula[0])

    bmc_check_end = time.time()
    global bmc_check_time
    bmc_check_time = bmc_check_end - bmc_check_start
    return guard_result, new_init_formula

def model_trans(model_var, model_value, bound):
    # print("model: ", model_var, type(model_var), "=", model_value, type(model_value))
    new_model = list()
    if isinstance(model_value, z3.DatatypeRef) or isinstance(model_value, z3.IntNumRef) or isinstance(model_value, z3.BoolRef):
        value = model_value
    elif model_value == None:
        pass
    else:
        value = model_value.as_string()

    if value != None:
        if str(model_var) in all_vars:
            new_model_var = str(model_var).rstrip(f"@{bound}") + "@0"
            if new_model_var in all_vars:
                new_model.append(all_vars[new_model_var][0] == value)
    
    return new_model
    

def init_worker(queue, init_fomula, axiom_formula, all_LTL_formula, upper_bound, inv, mfile_path, ScalarSetType_vars, BooleanType_vars, procount):
    # 使用传递的参数执行任务...
    inv_check_result, inv = mul_call_BMC(init_fomula, axiom_formula, all_LTL_formula, upper_bound, inv, mfile_path, ScalarSetType_vars, BooleanType_vars, procount)
    # print("inv_check_result: ", inv_check_result)
    queue.put(inv_check_result)

def run_parallel_tasks(inv, init_fomula, axiom_formula, all_LTL_formula, ScalarSetType_vars, BooleanType_vars, lower_procount, upper_procount, upper_bound, mfile_path, step_count):
    processes = []
    

    queue = Queue()
    # 创建并启动指定数量的工作线程
    for procount in range(lower_procount, upper_procount, step_count):
        # print("procount: ", procount)
        p = Process(target=init_worker, args=(queue, init_fomula, axiom_formula, all_LTL_formula, upper_bound, inv, mfile_path, ScalarSetType_vars, BooleanType_vars, procount))
        p.start()
        processes.append(p)

    results = []

    # for p in processes:
    #     p.join()

    while True:
        result = queue.get()
        # print("result: ", result)
        results.append(result)
        if result or (not result):
            for p in processes:
                p.terminate()  # 终止进程
            break
        

    if results:
        return results[-1]  # 返回终止进程的结果
    else:
        return []

def guard_work(queue, init_formula, axiom_formula, all_LTL_formula, upper_bound, check_inv, mfile_path, ScalarSetType_vars, BooleanType_vars):
    inv_check_result, inv = call_BMC(init_formula, axiom_formula, all_LTL_formula, upper_bound, check_inv, mfile_path, ScalarSetType_vars, BooleanType_vars)     
    queue.put(inv_check_result)

def mul_process_guard(check_inv, init_formula, all_init_formula, axiom_formula, all_LTL_formula, ScalarSetType_vars, BooleanType_vars, upper_bound, mfile_path):
    processes = []
    

    queue = Queue()
    # 创建并启动指定数量的工作线程
    for i in range(0, len(all_init_formula)+1):
        # print("process: ", i, all_init_formula[i])
        if i == 0:
            p = Process(target=guard_work, args=(queue, init_formula, axiom_formula, all_LTL_formula, upper_bound, check_inv, mfile_path, ScalarSetType_vars, BooleanType_vars))
            p.start()
            processes.append(p)
        else:
            if all_init_formula[i-1]:
                p = Process(target=guard_work, args=(queue, all_init_formula[i-1], axiom_formula, all_LTL_formula, upper_bound, check_inv, mfile_path, ScalarSetType_vars, BooleanType_vars))
                p.start()
                processes.append(p)

    results = []

    # for p in processes:
    #     p.join()

    while True:
        result = queue.get()
        # print("result: ", result)
        results.append(result)
        if result or (not result):
            for p in processes:
                p.terminate()  # 终止进程
            break
        

    if results:
        return results[-1]  # 返回终止进程的结果
    else:
        return []

if __name__ == "__main__":

    # inv = "!(n[1] = I & x = false)"   # false
    # inv = "!(n[1] = C & n[2] = C)"    # true
    # inv = "!(n[1] = T & n[2] = I)"    # false

    # inv = "!(ShrSet[1] = false & Cache[1].State = E)"   # true
    # inv = "!(InvSet[2] = false & Chan2[2].Cmd = Empty & CurCmd = Reqs & Cache[2].State = E)"    # false
    
    # inv = "!(Sta.NakcMsg.Cmd = NAKC_None & Sta.HomeProc.ProcCmd = NODE_None)"
    # inv = "!(Sta.UniMsg[2].Cmd = UNI_PutX)"

    # inv_path = "../protocols/mutualEx/mutualEx"
    # inv_path = "../protocols/german_withoutData/german_withoutData"
    # inv_path = "../protocols/flash_withoutData/flash_nodata_cub"

    # inv_path = "../protocols/mutual_nodata_benchmark/mutualEx_4"
    # mfile_path = "../protocols/mutualEx/mutualEx"

    # inv_path = "../protocols/german_data_benchmark/german_1"
    # inv_path = "../protocols/german_4/german_97"
    # mfile_path = "../protocols/german_withdata/german"

    # inv_path = "../protocols/flash_data_2/flash_1"
    # mfile_path = "../protocols/flash_withData/flash_data_cub"

    # inv_path = "../protocols/flash_3/flash_1"
    # mfile_path = "../protocols/flash_withoutData/flash_nodata_cub"

    # inv_path = "../protocols/decentralized_lock_inv/decen_9"
    # mfile_path = "../protocols/decentralized_lock/decentralized_lock"

    # inv_path = "../protocols/lock_server_inv/lock_server_1"
    # mfile_path = "../protocols/lock_server/lock_server"

    # inv_path = "../protocols/Ricart-Agrawala_inv/Ricart-Agrawala_1"
    # mfile_path = "../protocols/Ricart-Agrawala/Ricart-Agrawala"

    # inv_path = "../protocols/two_phase_commit_inv/two_phase_commit_1"
    # mfile_path = "../protocols/two_phase_commit/two_phase_commit"

    # inv_path = "../protocols/shard_inv/shard_1"
    # mfile_path = "../protocols/shard/shard"

    # inv_path = "../protocols/consensus_inv/consensus_2"
    # mfile_path = "../protocols/consensus/consensus"    # 最少需要 10 bounds

    # inv_path = "../protocols/paxos_inv/paxos_1"
    # mfile_path = "../protocols/paxos/paxos_bmc"

    inv_path = "../protocols/philosopher_inv/philosopher_1"
    mfile_path = "../protocols/philosopher/philosopher"

    with open(inv_path + ".m", 'r') as file:
        lines = file.readlines()
    # for line in lines:
    #     if "!(" in line:
    #         inv_str = line
    for i in range(len(lines)):
        line = lines[i]
        if "invariant" in line:
            next_line_idx = i + 1
            if next_line_idx < len(lines):
                inv_str = lines[next_line_idx]
    
    check_inv = inv_str.strip()
    

    # sys.stdout = open("./FileLog/" + inv_path.split("/")[-2] + 'BMCtest.log', 'w')
    # sys.stderr = open("./FileLog/" + inv_path.split("/")[-2] + 'BMCtest.log', 'w')

    upper_bound = 10
    lower_procount = 0
    upper_procount = 10
    step_count = 2


    s_check_time = time.time()

    s_formula_time = time.time()

    init_formula, axiom_formula, all_LTL_formula, ScalarSetType_vars, BooleanType_vars, negGuard_formula = get_BMC_formula(lower_procount, upper_procount, upper_bound, mfile_path)

    all_init_formula = list()
    for neguard in negGuard_formula:
        neg_guard = neguard
        # print("neg_guard: ", neg_guard, type(neg_guard))
        
        guard_result, new_init_formula = call_BMC_guard(init_formula, axiom_formula, all_LTL_formula, upper_bound, neg_guard, mfile_path, ScalarSetType_vars, BooleanType_vars)
        # inv_check_result, inv = call_BMC(new_init_formula, axiom_formula, all_LTL_formula, upper_bound, check_inv, mfile_path, ScalarSetType_vars, BooleanType_vars)
        
        if new_init_formula:
            all_init_formula.append(new_init_formula)
    # print(all_init_formula)
    e_formula_time = time.time()
    a_formula_time = e_formula_time - s_formula_time
    print(f"the time of bmc formula is {a_formula_time:.6f} s")

    s_bmc_time = time.time()
    # inv_check_result, inv = call_BMC(init_formula, axiom_formula, all_LTL_formula, upper_bound, check_inv, mfile_path, ScalarSetType_vars, BooleanType_vars)

    # results = run_parallel_tasks(inv, init_formula, axiom_formula, all_LTL_formula, ScalarSetType_vars, BooleanType_vars, lower_procount, upper_procount, upper_bound, mfile_path, step_count)
    results = mul_process_guard(check_inv, init_formula, all_init_formula, axiom_formula, all_LTL_formula, ScalarSetType_vars, BooleanType_vars, upper_bound, mfile_path)
    e_bmc_time = time.time()

    print("results: ", results)
    
    print("inv: ", check_inv)
    # print("inv_check_result: ", inv_check_result)
    
    a_bmc_time = e_bmc_time - s_bmc_time
    e_check_time = time.time()
    t_BMC = e_check_time - s_check_time
    print(f"the total times of bmc are {upper_bound} bound") 
    
    print(f"the time of bmc check is {a_bmc_time:.6f} s")
    print(f"Times of calling BMC spends {t_BMC:.6f} s")

    # pur_file_name = write_murphi(inv_path, pur_path, str_murphi)


    # sys.stdout.close()
    # sys.stderr.close()