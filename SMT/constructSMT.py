
from z3 import *
import os
import sys
import time
sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import murphi

# 获取根路径的绝对路径
sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from murphiparser import *
from murphi import *
import re
import copy
import itertools

# name_file = open('inv_name.txt', 'r', encoding='utf-8')
# self.dl_inv_name = name_file.read()  # inv 的 name
# self.dl_inv_name = "mutual"


class GetSMTformula:
    # dl_inv = dict()
    def __init__(self, protocol_name, parse_name, dl_inv = ""):
        """
        :param parse_name:  为 .m 文件路径
        :param node_permutations:  设置节点序号，比如两个节点即为 [1,2]
        """
        # print("parse_name: ", parse_name)
        # print("node_permutations: ", node_permutations)
        self.dl_inv_name = protocol_name
        self.protocol_name = protocol_name
        self.parse_name = parse_name
        self.prot = parse_file(parse_name+".m")  # .m 文件语法解析
        # print("prot: ", self.prot)
        # print(self.prot.rule_map)
        self.dl_inv = dl_inv
        # print("self.dl_inv: ", dl_inv, type(dl_inv))

        # 创建字典
        self.rule_para = dict()
        self.rule_var_map = dict()
        self.inv_para = dict()
        self.inv_var_map = dict()
        self.inv_array_var_map = dict()
        self.inv_var_length = dict()
        self.inv_var_ins = dict()
        self.inv_instance = dict()
        self.rule_var_ins = dict()
        self.rule_instance = dict()
        self.ins_var4rule = list()
        self.ins_var_dict = dict()
        self.formula_instances = dict()
        self.deduction = dict()
        self.arrayVar_insLength = dict()

        self.ins_var = None

        self.booleanExpr_list = list()

        self.enum_typ_map = self.prot.enum_typ_map  # 字典形式，存储的是协议中所有的 enum 类型

        self.typ_map = self.prot.typ_map  # 字典形式，存储的是协议中所有的 type 类型

        self.scalarsetType = self.prot.scalarset  # 字典形式， 存储的是协议中所有的 scalarset 类型
        self.scalarsetVars = list()

        self.invariant_ins = dict()
        self.all_guard = list()  # 用于存储所有的 guard
        self.inv_init_smt = list()

        self.rule_dl_map = dict()
        self.dp_list = list()
        self.rule_var_list = dict()

        self.all_rule_dict = dict()

        self.enum_var = dict()
        self.key_enum = dict()

        self.all_ins_vars = dict()

        self.init_instance = dict()

        self.axiom_instance = dict()

        self.all_init_formula = list()

        self.all_init_dict = dict()
        self.arr_idx = dict()

    def get_character(self, node_number):
        node_permutations = list()
        node_list = list()
        for i in range(1, node_number + 1):
            node_permutations.append(i)
            node_list.append(chr(ord('i') + int(i) - 1))
        return node_permutations, node_list

    def join_statements(self,statement):
        if len(statement) == 1:
            return statement[0]
        else:
            # return (str(statement[-1]) + "& (" + self.join_statements(statement[:-1]) + ")")
            # OpExpr(self, op, expr1, expr2):
            return murphi.OpExpr('&',statement[-1],self.join_statements(statement[:-1]))
    
    def disjoin_statements(self,statement):
        if len(statement) == 1:
            return statement[0]
        else:
            # return (str(statement[-1]) + "| (" + self.join_statements(statement[:-1]) + ")")
            return murphi.OpExpr('|',statement[-1],self.join_statements(statement[:-1]))

    def mathOp2ins(self, mathOp, inv_var_ins, inv_var_map,var_typ):
        expr1_digit = False
        expr2_digit = False
        if isinstance(mathOp.expr1, murphi.OpExpr):
            self.mathOp2ins(mathOp.expr1, inv_var_ins, inv_var_map,var_typ)
        else:
            expr1_digit = True
            if str(mathOp.expr1).isdigit():
                pass
            else:
                if mathOp.expr1.name in inv_var_map.keys() and mathOp.expr1.name in inv_var_ins.keys():
                    var_typ = inv_var_map[mathOp.expr1.name]
                    mathOp.expr1.name = mathOp.expr1.name.replace(mathOp.expr1.name,
                                                                          str(inv_var_ins[mathOp.expr1.name]))

        if isinstance(mathOp.expr2, murphi.OpExpr):
            self.mathOp2ins(mathOp.expr2, inv_var_ins, inv_var_map,var_typ)
        else:
            expr2_digit = True
            if str(mathOp.expr2).isdigit():
                pass
            else:
                if mathOp.expr2.name in inv_var_map.keys() and mathOp.expr2.name in inv_var_ins.keys():
                    var_typ = inv_var_map[mathOp.expr2.name]
                    mathOp.expr2.name = mathOp.expr2.name.replace(mathOp.expr2.name,
                                                                          str(inv_var_ins[mathOp.expr2.name]))
        if expr1_digit and expr2_digit:
            mathOp = str(mathOp).replace('/','//')
            mathVal = eval(mathOp)
            murphi_idx = murphi.VarExpr(name=str(mathVal),typ=var_typ)
            return murphi_idx

    # Converting formulas from parameterized form to instantiated formulas
    def para2ins(self, OpExpr, inv_var_ins, inv_var_map,ins_var_list2,inv_allVars_map, forinv=False):  
        # print(OpExpr, inv_var_ins, inv_var_map,ins_var_list2,inv_allVars_map)   
        if isinstance(OpExpr, murphi.ArrayIndex):
            # 多维数组
            if isinstance(OpExpr.v, FieldName):
                self.para2ins(OpExpr.v, inv_var_ins, inv_var_map,ins_var_list2,inv_allVars_map, forinv)
            if isinstance(OpExpr.v, murphi.ArrayIndex):
                self.para2ins(OpExpr.v, inv_var_ins, inv_var_map,ins_var_list2,inv_allVars_map, forinv)

            # assert isinstance(OpExpr.idx, murphi.VarExpr)
            if isinstance(OpExpr.idx, murphi.VarExpr):
                if OpExpr.idx.name in inv_var_map.keys() and OpExpr.idx.name in inv_var_ins.keys():
                    OpExpr.idx.name = OpExpr.idx.name.replace(OpExpr.idx.name, str(inv_var_ins[OpExpr.idx.name]))
                # self.ins_var4rule = OpExpr.var
            if OpExpr not in self.ins_var4rule and str(OpExpr) in murphi.specific_var.keys():
                self.ins_var4rule.append(OpExpr)
            if OpExpr not in ins_var_list2 and str(OpExpr) in murphi.specific_var.keys():
                ins_var_list2.append(OpExpr)

        elif isinstance(OpExpr, murphi.AssignCmd):
            if isinstance(OpExpr.expr, murphi.FieldName):
                if isinstance(OpExpr.expr.v, FieldName):
                    self.para2ins(OpExpr.expr.v, inv_var_ins, inv_var_map,ins_var_list2,inv_allVars_map, forinv)
                
                if isinstance(OpExpr.expr.v, murphi.ArrayIndex):
                    if isinstance(OpExpr.expr.v.v, ArrayIndex):
                        self.para2ins(OpExpr.expr.v.v, inv_var_ins, inv_var_map,ins_var_list2,inv_allVars_map, forinv)
                    elif isinstance(OpExpr.expr.v.v, FieldName):
                        self.para2ins(OpExpr.expr.v.v, inv_var_ins, inv_var_map,ins_var_list2,inv_allVars_map, forinv)
                    
                    if isinstance(OpExpr.expr.v.idx, murphi.OpExpr):
                        OpExpr.expr.v.idx = self.mathOp2ins(OpExpr.expr.v.idx, inv_var_ins, inv_var_map, None)
                    # assert isinstance(OpExpr.expr.v.idx, murphi.VarExpr)
                    elif isinstance(OpExpr.expr.v.idx, murphi.VarExpr):
                        if OpExpr.expr.v.idx.name in inv_var_map.keys() and OpExpr.expr.v.idx.name in inv_var_ins.keys():
                            OpExpr.expr.v.idx.name = OpExpr.expr.v.idx.name.replace(OpExpr.expr.v.idx.name,
                                                                                str(inv_var_ins[OpExpr.expr.v.idx.name]))

                if OpExpr.expr not in ins_var_list2 and str(OpExpr.expr) in murphi.specific_var.keys():
                    ins_var_list2.append(OpExpr.expr)

            elif isinstance(OpExpr.expr, murphi.VarExpr):
                if OpExpr.expr.name in inv_var_map.keys() and OpExpr.expr.name in inv_var_ins.keys():
                    OpExpr.expr.name = OpExpr.expr.name.replace(OpExpr.expr.name,
                                                                      str(inv_var_ins[OpExpr.expr.name]))

                    if OpExpr.expr not in ins_var_list2 and not str(OpExpr.expr).isdigit() and str(OpExpr.expr) in murphi.specific_var.keys():
                        ins_var_list2.append(OpExpr.expr)

            elif isinstance(OpExpr.expr, murphi.ArrayIndex):
                # 多维数组
                if isinstance(OpExpr.expr.v, FieldName):
                    self.para2ins(OpExpr.expr.v, inv_var_ins, inv_var_map,ins_var_list2,inv_allVars_map, forinv)
                if isinstance(OpExpr.expr.v, murphi.ArrayIndex):
                    self.para2ins(OpExpr.expr.v, inv_var_ins, inv_var_map,ins_var_list2,inv_allVars_map, forinv)

                assert isinstance(OpExpr.expr.idx, murphi.VarExpr)
                if OpExpr.expr.idx.name in inv_var_map.keys() and OpExpr.expr.idx.name in inv_var_ins.keys():
                    OpExpr.expr.idx.name = OpExpr.expr.idx.name.replace(OpExpr.expr.idx.name,
                                                                      str(inv_var_ins[OpExpr.expr.idx.name]))
                    if OpExpr.expr not in ins_var_list2 and str(OpExpr.expr) in murphi.specific_var.keys():
                        ins_var_list2.append(OpExpr.expr)

            elif isinstance(OpExpr.expr, murphi.OpExpr):
                mathpattern = r'[-+*/%]'
                logicpattern = r'[!&|=->]'
                if re.search(mathpattern, str(OpExpr.expr)) is not None and re.search(logicpattern, str(OpExpr.expr)) is None:
                    OpExpr.expr = self.mathOp2ins(OpExpr.expr,inv_var_ins, inv_var_map, None)
                else:
                    self.para2ins(OpExpr.expr, inv_var_ins, inv_var_map,ins_var_list2,inv_allVars_map, forinv)
                # self.para2ins(OpExpr.expr, inv_var_ins, inv_var_map,ins_var_list2,inv_allVars_map, forinv)

            if isinstance(OpExpr.var, murphi.ArrayIndex):
                # 多维数组
                if isinstance(OpExpr.var.v, FieldName):
                    self.para2ins(OpExpr.var.v, inv_var_ins, inv_var_map,ins_var_list2,inv_allVars_map, forinv)
                if isinstance(OpExpr.var.v, murphi.ArrayIndex):
                    self.para2ins(OpExpr.var.v, inv_var_ins, inv_var_map,ins_var_list2,inv_allVars_map, forinv)

                assert isinstance(OpExpr.var.idx, murphi.VarExpr)

                if OpExpr.var.idx.name in inv_var_map.keys() and OpExpr.var.idx.name in inv_var_ins.keys():
                    OpExpr.var.idx.name = OpExpr.var.idx.name.replace(OpExpr.var.idx.name, str(inv_var_ins[OpExpr.var.idx.name]))
                    # self.ins_var4rule = OpExpr.var
                    if OpExpr.var not in self.ins_var4rule and str(OpExpr.var) in murphi.specific_var.keys():
                        self.ins_var4rule.append(OpExpr.var)
                    if OpExpr.var not in ins_var_list2 and str(OpExpr.var) in murphi.specific_var.keys():
                        ins_var_list2.append(OpExpr.var)

            elif isinstance(OpExpr.var, murphi.FieldName):
                if isinstance(OpExpr.var.v, FieldName):
                    self.para2ins(OpExpr.var.v, inv_var_ins, inv_var_map,ins_var_list2,inv_allVars_map, forinv)
                                
                if isinstance(OpExpr.var.v, murphi.ArrayIndex):
                    if isinstance(OpExpr.var.v.v, ArrayIndex):
                        self.para2ins(OpExpr.var.v.v, inv_var_ins, inv_var_map,ins_var_list2,inv_allVars_map, forinv)
                    elif isinstance(OpExpr.var.v.v, FieldName):
                        self.para2ins(OpExpr.var.v.v, inv_var_ins, inv_var_map,ins_var_list2,inv_allVars_map, forinv)
                                        
                    if isinstance(OpExpr.var.v.idx, murphi.OpExpr):
                        OpExpr.var.v.idx = self.mathOp2ins(OpExpr.var.v.idx, inv_var_ins, inv_var_map, None)
                    # assert isinstance(OpExpr.var.v.idx, murphi.VarExpr)
                    elif isinstance(OpExpr.var.v.idx, murphi.VarExpr):
                        if OpExpr.var.v.idx.name in inv_var_map.keys() and OpExpr.var.v.idx.name in inv_var_ins.keys():
                            OpExpr.var.v.idx.name = OpExpr.var.v.idx.name.replace(OpExpr.var.v.idx.name,
                                                                            str(inv_var_ins[OpExpr.var.v.idx.name]))
                        # self.ins_var4rule = OpExpr.var
                if OpExpr.var not in self.ins_var4rule and str(OpExpr.var) in murphi.specific_var.keys():
                    self.ins_var4rule.append(OpExpr.var)
                if OpExpr.var not in ins_var_list2 and str(OpExpr.var) in murphi.specific_var.keys():
                    ins_var_list2.append(OpExpr.var)
            elif isinstance(OpExpr.var, murphi.VarExpr):
                # self.ins_var4rule = OpExpr.var
                if OpExpr.var not in self.ins_var4rule and not str(OpExpr.var).isdigit() and str(OpExpr.var) in murphi.specific_var.keys():
                    self.ins_var4rule.append(OpExpr.var)
                if OpExpr.var not in ins_var_list2 and not str(OpExpr.var).isdigit() and str(OpExpr.var) in murphi.specific_var.keys():
                    ins_var_list2.append(OpExpr.var)

            elif isinstance(OpExpr.var, murphi.OpExpr):
                self.para2ins(OpExpr.var, inv_var_ins, inv_var_map,ins_var_list2,inv_allVars_map, forinv)

        elif isinstance(OpExpr, murphi.ForallCmd):

            # if OpExpr.typ in inv_var_map.values():
            expandingExpr = []
            var_length = self.arrayVar_insLength[str(OpExpr.typ)]
            for i in range(1, var_length + 1):
                ep_dp = copy.deepcopy(OpExpr.cmds)
                ins_dict_ep = copy.deepcopy(inv_var_ins)
                var_map_ep = copy.deepcopy(inv_var_map)
                ins_dict_ep[str(OpExpr.var)] = i
                var_map_ep[str(OpExpr.var)] = OpExpr.typ
                for sub_ep in ep_dp:
                    ins_ep = self.para2ins(sub_ep, ins_dict_ep, var_map_ep, ins_var_list2, inv_allVars_map, forinv)
                    # expandingExpr.append(ins_ep)
                    if isinstance(ins_ep, list):
                        expandingExpr.extend(ins_ep)
                    else:
                        expandingExpr.append(ins_ep)
            OpExpr = expandingExpr
        
        elif isinstance(OpExpr, murphi.ExistsExpr):
            expandingExpr = []
            var_length = self.arrayVar_insLength[str(OpExpr.typ)]
            for i in range(1,var_length+1):
                ep2_dp = copy.deepcopy(OpExpr.expr)
                ins_dict_ep2 = copy.deepcopy(inv_var_ins)
                var_map_ep2 = copy.deepcopy(inv_var_map)
                ins_dict_ep2[str(OpExpr.var)] = i
                var_map_ep2[str(OpExpr.var)] = OpExpr.typ
                ins_ep2 = self.para2ins(ep2_dp, ins_dict_ep2, var_map_ep2, ins_var_list2, inv_allVars_map, forinv)
                # expandingExpr.append(ins_ep2)
                if isinstance(ins_ep2, list):
                    expandingExpr.extend(ins_ep2)
                else:
                    expandingExpr.append(ins_ep2)
            disjoin_statements = self.disjoin_statements(expandingExpr)

            OpExpr = disjoin_statements

        elif isinstance(OpExpr, murphi.ForallExpr):
            # if OpExpr.typ in inv_var_map.values():
            expandingExpr = []
            var_length = self.arrayVar_insLength[str(OpExpr.typ)]
            for i in range(1,var_length+1):
                ep2_dp = copy.deepcopy(OpExpr.expr)
                ins_dict_ep2 = copy.deepcopy(inv_var_ins)
                var_map_ep2 = copy.deepcopy(inv_var_map)
                ins_dict_ep2[str(OpExpr.var)] = i
                var_map_ep2[str(OpExpr.var)] = OpExpr.typ
                ins_ep2 = self.para2ins(ep2_dp, ins_dict_ep2, var_map_ep2, ins_var_list2, inv_allVars_map, forinv)
                # expandingExpr.append(ins_ep2)
                if isinstance(ins_ep2, list):
                    expandingExpr.extend(ins_ep2)
                else:
                    expandingExpr.append(ins_ep2)
            join_statements = self.join_statements(expandingExpr)

            OpExpr = join_statements


        elif isinstance(OpExpr, murphi.OpExpr):
            if isinstance(OpExpr.expr1, murphi.OpExpr):
                self.para2ins(OpExpr.expr1, inv_var_ins, inv_var_map,ins_var_list2,inv_allVars_map, forinv)
            elif isinstance(OpExpr.expr1, murphi.NegExpr):
                OpExpr.expr1.expr = self.para2ins(OpExpr.expr1.expr, inv_var_ins, inv_var_map, ins_var_list2, inv_allVars_map, forinv)
            elif isinstance(OpExpr.expr1, murphi.ArrayIndex):
                # 多维数组
                if isinstance(OpExpr.expr1.v, FieldName):
                    self.para2ins(OpExpr.expr1.v, inv_var_ins, inv_var_map,ins_var_list2,inv_allVars_map, forinv)
                if isinstance(OpExpr.expr1.v, murphi.ArrayIndex):
                    self.para2ins(OpExpr.expr1.v, inv_var_ins, inv_var_map,ins_var_list2,inv_allVars_map, forinv)

                # assert isinstance(OpExpr.expr1.idx, murphi.VarExpr)
                if isinstance(OpExpr.expr1.idx, murphi.VarExpr):
                    if OpExpr.expr1.idx.name in inv_var_map.keys() and OpExpr.expr1.idx.name in inv_var_ins.keys():
                        OpExpr.expr1.idx.name = OpExpr.expr1.idx.name.replace(OpExpr.expr1.idx.name,
                                                                        str(inv_var_ins[OpExpr.expr1.idx.name]))
                if OpExpr.expr1 not in ins_var_list2 and str(OpExpr.expr1) in murphi.specific_var.keys():
                    ins_var_list2.append(OpExpr.expr1)
                if forinv:
                    self.ins_var = ins_var_list2
            elif isinstance(OpExpr.expr1, murphi.VarExpr):
                if OpExpr.expr1.name in inv_var_map.keys() and OpExpr.expr1.name in inv_var_ins.keys():
                    OpExpr.expr1.name = OpExpr.expr1.name.replace(OpExpr.expr1.name, str(inv_var_ins[OpExpr.expr1.name]))
                elif OpExpr.expr1.name in inv_allVars_map.keys():
                    if OpExpr.expr1 not in ins_var_list2 and not str(OpExpr.expr1).isdigit() and str(OpExpr.expr1) in murphi.specific_var.keys():
                        ins_var_list2.append(OpExpr.expr1)
                    if forinv:
                        self.ins_var = ins_var_list2
            elif isinstance(OpExpr.expr1, murphi.FieldName):
                if isinstance(OpExpr.expr1.v, FieldName):
                    self.para2ins(OpExpr.expr1.v, inv_var_ins, inv_var_map,ins_var_list2,inv_allVars_map, forinv)
                
                if isinstance(OpExpr.expr1.v, murphi.ArrayIndex):
                    if isinstance(OpExpr.expr1.v.v, ArrayIndex):
                        self.para2ins(OpExpr.expr1.v.v, inv_var_ins, inv_var_map,ins_var_list2,inv_allVars_map, forinv)
                    elif isinstance(OpExpr.expr1.v.v, FieldName):
                        self.para2ins(OpExpr.expr1.v.v, inv_var_ins, inv_var_map,ins_var_list2,inv_allVars_map, forinv)
                    
                    if isinstance(OpExpr.expr1.v.idx, murphi.OpExpr):
                        OpExpr.expr1.v.idx = self.mathOp2ins(OpExpr.expr1.v.idx, inv_var_ins, inv_var_map, None)
                    # assert isinstance(OpExpr.expr1.v.idx, murphi.VarExpr)
                    elif isinstance(OpExpr.expr1.v.idx, murphi.VarExpr):
                        if OpExpr.expr1.v.idx.name in inv_var_map.keys() and OpExpr.expr1.v.idx.name in inv_var_ins.keys():
                            OpExpr.expr1.v.idx.name = OpExpr.expr1.v.idx.name.replace(OpExpr.expr1.v.idx.name,
                                                                            str(inv_var_ins[OpExpr.expr1.v.idx.name]))
                if OpExpr.expr1 not in ins_var_list2 and str(OpExpr.expr1) in murphi.specific_var.keys():
                    ins_var_list2.append(OpExpr.expr1)
                if forinv:
                    self.ins_var = ins_var_list2
            elif isinstance(OpExpr.expr1, murphi.ForallExpr):
                # if OpExpr.expr1.typ in inv_var_map.values():
                expandingExpr = []
                var_length = self.arrayVar_insLength[str(OpExpr.expr1.typ)]
                for i in range(1, var_length + 1):
                    ep1_dp = copy.deepcopy(OpExpr.expr1.expr)
                    ins_dict_ep1 = copy.deepcopy(inv_var_ins)
                    var_map_ep1 = copy.deepcopy(inv_var_map)
                    ins_dict_ep1[str(OpExpr.expr1.var)] = i
                    var_map_ep1[str(OpExpr.expr1.var)] = OpExpr.expr1.typ
                    ins_ep1 = self.para2ins(ep1_dp, ins_dict_ep1, var_map_ep1, ins_var_list2, inv_allVars_map, forinv)
                    # expandingExpr.append(ins_ep1)
                    if isinstance(ins_ep1, list):
                        expandingExpr.extend(ins_ep1)
                    else:
                        expandingExpr.append(ins_ep1)
                join_statements = self.join_statements(expandingExpr)
                OpExpr.expr1 = join_statements
            else:
                pass

            if isinstance(OpExpr.expr2, murphi.OpExpr):
                mathpattern = r'[-+*/%]'
                logicpattern = r'[!&|=->]'
                if re.search(mathpattern, str(OpExpr.expr2)) is not None and re.search(logicpattern, str(OpExpr.expr2)) is None:
                    OpExpr.expr2 = self.mathOp2ins(OpExpr.expr2,inv_var_ins, inv_var_map, None)
                else:
                    self.para2ins(OpExpr.expr2, inv_var_ins, inv_var_map,ins_var_list2,inv_allVars_map, forinv)
            elif isinstance(OpExpr.expr2, murphi.NegExpr):
                OpExpr.expr2.expr = self.para2ins(OpExpr.expr2.expr, inv_var_ins, inv_var_map, ins_var_list2, inv_allVars_map, forinv)
            elif isinstance(OpExpr.expr2, murphi.ArrayIndex):
                # 多维数组
                if isinstance(OpExpr.expr2.v, murphi.ArrayIndex):
                    self.para2ins(OpExpr.expr2.v, inv_var_ins, inv_var_map,ins_var_list2,inv_allVars_map, forinv)

                # print(OpExpr.expr2, OpExpr.expr2.idx)
                assert isinstance(OpExpr.expr2.idx, murphi.VarExpr)
                
                if OpExpr.expr2.idx.name in inv_var_map.keys() and OpExpr.expr2.idx.name in inv_var_ins.keys():
                    OpExpr.expr2.idx.name = OpExpr.expr2.idx.name.replace(OpExpr.expr2.idx.name,
                                                                      str(inv_var_ins[OpExpr.expr2.idx.name]))
                if OpExpr.expr2 not in ins_var_list2 and str(OpExpr.expr2) in murphi.specific_var.keys():
                    ins_var_list2.append(OpExpr.expr2)
                if forinv:
                    self.ins_var = ins_var_list2
            elif isinstance(OpExpr.expr2, murphi.VarExpr):
                # print("inv_var_ins:",inv_var_ins)
                if OpExpr.expr2.name in inv_var_map.keys() and OpExpr.expr2.name in inv_var_ins.keys():
                    OpExpr.expr2.name = OpExpr.expr2.name.replace(OpExpr.expr2.name, str(inv_var_ins[OpExpr.expr2.name]))
                elif OpExpr.expr2.name in inv_allVars_map.keys():
                    if OpExpr.expr2 not in ins_var_list2 and not str(OpExpr.expr2).isdigit() and str(OpExpr.expr2) in murphi.specific_var.keys():
                        ins_var_list2.append(OpExpr.expr2)
                    if forinv:
                        self.ins_var = ins_var_list2
            elif isinstance(OpExpr.expr2, murphi.FieldName):
                if isinstance(OpExpr.expr2.v, FieldName):
                    self.para2ins(OpExpr.expr2.v, inv_var_ins, inv_var_map,ins_var_list2,inv_allVars_map, forinv)
                             
                if isinstance(OpExpr.expr2.v, murphi.ArrayIndex):
                    if isinstance(OpExpr.expr2.v.v, ArrayIndex):
                        self.para2ins(OpExpr.expr2.v.v, inv_var_ins, inv_var_map,ins_var_list2,inv_allVars_map, forinv)
                    elif isinstance(OpExpr.expr2.v.v, FieldName):
                        self.para2ins(OpExpr.expr2.v.v, inv_var_ins, inv_var_map,ins_var_list2,inv_allVars_map, forinv)
                    
                    if isinstance(OpExpr.expr2.v.idx, murphi.OpExpr):
                        OpExpr.expr2.v.idx = self.mathOp2ins(OpExpr.expr2.v.idx, inv_var_ins, inv_var_map, None)            
                    # assert isinstance(OpExpr.expr2.v.idx, murphi.VarExpr)
                    elif isinstance(OpExpr.expr2.v.idx, murphi.VarExpr):
                        if OpExpr.expr2.v.idx.name in inv_var_map.keys() and OpExpr.expr2.v.idx.name in inv_var_ins.keys():
                            OpExpr.expr2.v.idx.name = OpExpr.expr2.v.idx.name.replace(OpExpr.expr2.v.idx.name,
                                                                            str(inv_var_ins[OpExpr.expr2.v.idx.name]))
                if OpExpr.expr2 not in ins_var_list2 and str(OpExpr.expr2) in murphi.specific_var.keys():
                    ins_var_list2.append(OpExpr.expr2)
                if forinv:
                    self.ins_var = ins_var_list2
            elif isinstance(OpExpr.expr2, murphi.ForallExpr):
                # if OpExpr.expr2.typ in inv_var_map.values():
                expandingExpr = []
                var_length = self.arrayVar_insLength[str(OpExpr.expr2.typ)]
                for i in range(1,var_length+1):
                    ep2_dp = copy.deepcopy(OpExpr.expr2.expr)
                    ins_dict_ep2 = copy.deepcopy(inv_var_ins)
                    var_map_ep2 = copy.deepcopy(inv_var_map)
                    ins_dict_ep2[str(OpExpr.expr2.var)] = i
                    var_map_ep2[str(OpExpr.expr2.var)] = OpExpr.expr2.typ
                    ins_ep2 = self.para2ins(ep2_dp, ins_dict_ep2, var_map_ep2, ins_var_list2, inv_allVars_map, forinv)
                    # expandingExpr.append(ins_ep2)
                    if isinstance(ins_ep2, list):
                        expandingExpr.extend(ins_ep2)
                    else:
                        expandingExpr.append(ins_ep2)
                join_statements = self.join_statements(expandingExpr)
                OpExpr.expr2 = join_statements
            else:
                pass

        elif isinstance(OpExpr, IfCmd):
            self.para2ins(OpExpr.if_branches[0][0], inv_var_ins, inv_var_map, ins_var_list2, inv_allVars_map, forinv)
            for ifassign in OpExpr.if_branches[0][1]:
                self.para2ins(ifassign, inv_var_ins, inv_var_map, ins_var_list2, inv_allVars_map, forinv)
            if OpExpr.else_branch:
                for elseassign in OpExpr.else_branch:
                    self.para2ins(elseassign, inv_var_ins, inv_var_map, ins_var_list2, inv_allVars_map, forinv)

        elif isinstance(OpExpr, murphi.NegExpr):
            OpExpr.expr = self.para2ins(OpExpr.expr, inv_var_ins, inv_var_map,ins_var_list2,inv_allVars_map, forinv)
        else:
            pass

        return OpExpr


    def get_sub_init(self, cmd, init_state, init_var, init_var_map):
        if isinstance(cmd, murphi.ForallCmd):
            # print(cmd.var_decl, cmd.var, cmd.typ)
            if isinstance(cmd.var, str):
                init_var.append(cmd.var)
                # print("cmd.typ: ", cmd.typ)
                init_var_map[cmd.var] = cmd.typ
                var_type = cmd.typ
            for sub_cmd in cmd.cmds:
                # print("sub_cmd: ", sub_cmd, type(sub_cmd))
                self.get_sub_init(sub_cmd, init_state, init_var, init_var_map)
        if isinstance(cmd, murphi.AssignCmd):
            assign_init = murphi.OpExpr("=", cmd.var, cmd.expr)
            init_state.append(assign_init)
        if isinstance(cmd, murphi.OpExpr):
            # if cmd.op == '->':
            #     imply_init = murphi.OpExpr("|", murphi.NegExpr(cmd.expr1), cmd.expr2)
            #     init_state.append(imply_init)
            # else:
            init_state.append(cmd)
        return init_state, init_var, init_var_map
    
    def get_allExpr(self, equal):
        if isinstance(equal, murphi.OpExpr):
            if isinstance(equal.expr1, murphi.OpExpr):
                self.get_allExpr(equal.expr1)
            elif isinstance(equal.expr1, murphi.NegExpr):
                self.get_allExpr(equal.expr1.expr)
            else:
                # print("equal: ", equal)
                if str(equal.expr1) not in self.all_init_dict:
                    self.all_init_dict[str(equal.expr1)] = equal.expr1
                if str(equal.expr1) not in self.all_ins_vars:
                    if isinstance(equal.expr1, murphi.BooleanExpr):
                        pass
                    if str(equal.expr1).isdigit():
                        pass
                    else:
                        # print(equal.expr1, type(equal.expr1))
                        self.all_ins_vars[str(equal.expr1)] = equal.expr1
                    # print(self.all_ins_vars)
            if isinstance(equal.expr2, murphi.OpExpr):
                self.get_allExpr(equal.expr2)
            elif isinstance(equal.expr2, murphi.NegExpr):
                self.get_allExpr(equal.expr2.expr)
            else:
                if str(equal.expr2) not in self.all_init_dict:
                    self.all_init_dict[str(equal.expr2)] = equal.expr2
                if str(equal.expr2) not in self.all_ins_vars:
                    if isinstance(equal.expr2, murphi.VarExpr) or isinstance(equal.expr2, murphi.BooleanExpr):
                        pass
                    else:
                        # print(equal.expr2, type(equal.expr2))
                        self.all_ins_vars[str(equal.expr1)] = equal.expr1
        
        elif isinstance(equal, murphi.NegExpr):
            self.get_allExpr(equal.expr)
        
        # print(self.all_ins_vars)

    def var_Eq_expr(self, var, expr):
        # print(var, expr)
        if isinstance(expr, murphi.OpExpr):
            return self.var_Eq_expr(var, expr.expr1) | self.var_Eq_expr(var, expr.expr2)
        elif isinstance(expr, murphi.VarExpr):
            if str(expr) == var:
                return True
            else:
                return False
        return False
    
    def expr_is_Var(self, expr):
        if isinstance(expr, murphi.OpExpr):
            return self.expr_is_Var(expr.expr1) | self.expr_is_Var(expr.expr2)
        elif str(expr).isdigit():
            return True
        elif isinstance(expr, murphi.VarExpr):
            return True
        else:
            return False

    def getInit(self):
        init_state = list()
        init_var = list()
        init_var_map = dict()
        init_instance_rule = dict()
        init_sub_instance = list()
        ruleset_var = list()
        ruleset_var_map = dict()
        if isinstance(self.prot.start_state, murphi.MurphiRuleSet):
            # 这部分是考虑到使用 ruleset，而不是 for 循环
            # print(self.prot.start_state.var_map)
            for var_str, var_typ in self.prot.start_state.var_map.items():
                ruleset_var.append(var_str)
                ruleset_var_map[var_str] = var_typ
            start_state_rule = self.prot.start_state.rule
            startstate_name = start_state_rule.name
            for cmd in start_state_rule.cmds:
                # print(cmd, type(cmd))
                init_state, init_var, init_var_map = self.get_sub_init(cmd, init_state, init_var, init_var_map)
            
            consts_dict = dict()
            for const in self.prot.consts:
                if isinstance(const, murphi.MurphiConstDecl):
                    consts_dict[const.name] = int(str(const.val))
                    # print("const.name: ", const.name, "const.val: ", const.val)

            types_dict = dict()
            for typs in self.prot.types:
                # print("typ: ", typs, type(typs))
                assert isinstance(typs, murphi.MurphiTypeDecl)
                if isinstance(typs.typ, murphi.ScalarSetType):
                    types_dict[typs.name] = typs.typ.const_name
                if isinstance(typs.typ, murphi.RngType):
                    types_dict[typs.name] = typs.typ.upRng

            ruleset_value = dict()

            # print("ruleset_var_map: ", ruleset_var_map)
            # print("init_var_map: ", init_var_map)
            for rule_str, rule_typ in ruleset_var_map.items():
                assert isinstance(rule_typ, murphi.VarType)
                # print("rule_typ: ", rule_typ, rule_typ.name)
                for consts_str, consts_typ in consts_dict.items():
                    for types_str, types_typ in types_dict.items():
                        if types_typ == consts_str:
                            if rule_typ.name == types_str:
                                ruleset_value[rule_str] = consts_typ
            # print("ruleset_value: ", ruleset_value)

            init_value = dict()
            for init_str, init_typ in init_var_map.items():
                assert isinstance(init_typ, murphi.VarType)
                for consts_str, consts_typ in consts_dict.items():
                    for types_str, types_typ in types_dict.items():
                        if types_typ == consts_str:
                            if init_typ.name == types_str:
                                init_value[init_str] = consts_typ
            # print("init_value: ", init_value)
                                
            all_var_value = dict()
            all_var_value = {**ruleset_value, **init_value}
            # print("all_var_value: ", all_var_value)

            ruleset_str_dict = dict()
            
            for rule_key, rule_val in ruleset_value.items():
                node_per_tmp, _ = self.get_character(rule_val)
                node_str_list = list(itertools.product(copy.deepcopy(node_per_tmp), repeat = len(node_per_tmp)))
                for var_key, var_value in ruleset_var_map.items():
                    if rule_key == var_key:
                        ruleset_str = [{key: value for key, value in zip(var_key, combo)} for combo in node_str_list]
                        ruleset_str = [dict(t) for t in {tuple(d.items()) for d in ruleset_str}]
                        ruleset_str_dict[rule_key] = ruleset_str
                
            node_var_list = init_var

            init_str_list = list()
            for init_key, init_val in init_value.items():
                init_node_per, _ = self.get_character(init_val)
                init_str_list = list(itertools.product(copy.deepcopy(init_node_per), repeat = len(init_node_per)))
            if init_str_list:
                node_str = [{key: value for key, value in zip(init_var, combo)} for combo in init_str_list]
                node_str = [dict(t) for t in {tuple(d.items()) for d in node_str}]
            else:
                for _, rv in ruleset_value.items():
                    init_str_tmp, _ = self.get_character(rv)
                init_str_list = list(itertools.product(copy.deepcopy(init_str_tmp), repeat = len(init_str_tmp)))
                node_str = [{key: value for key, value in zip(node_var_list, combo)} for combo in init_str_list]
                node_str = [dict(t) for t in {tuple(d.items()) for d in node_str}]
                # print("init_str_list: ", init_str_list, node_str)

            # print(node_str_list, node_str, init_var_map)
            # print("ruleset_str_dict: ", ruleset_str_dict)

            init_instance_tmp = list()

            # print("init_state: ", init_state)
            # print("ruleset_var: ", ruleset_var, "init_var: ", init_var)

            is_or = False

            cache_is_or = False

            for init in init_state:
                # print("init: ", init)
                assert isinstance(init, murphi.OpExpr)
                if node_str:
                    for var in node_str:
                        ini_state = copy.deepcopy(init)
                        init_sub_state = self.para2ins(ini_state, var, init_var_map, [], {})
                        # print(ini_state, var, init_var_map, init_sub_state, init_sub_state in init_sub_instance)
                        if init_sub_state not in init_instance_tmp:
                            init_instance_tmp.append(init_sub_state)
                # print("init: ", init.expr1, init.expr2, type(init.expr1))
                
                arr_tmp = list()
                if isinstance(init.expr1, murphi.ArrayIndex):
                    # print("init.expr1: ", init.expr1.v, init.expr1.idx, type(init.expr1.v))
                    for init_str, init_val in all_var_value.items():
                        if isinstance(init.expr1.v, murphi.ArrayIndex):
                            if init_str == str(init.expr1.v.idx):
                                arr_tmp.append(init_val)
                            if init_str == str(init.expr1.idx):
                                arr_tmp.append(init_val)
                            if arr_tmp:
                                self.arr_idx[str(init.expr1.v.v)] = arr_tmp
                        else:
                            if init_str == str(init.expr1.idx):
                                arr_tmp.append(init_val)
                            if arr_tmp:
                                self.arr_idx[str(init.expr1.v)] = arr_tmp
                
                if len(ruleset_var) > 1:
                    for r_var in ruleset_var:
                        # if r_var == str(init.expr2):
                        #     is_or = True
                        eq_result = self.var_Eq_expr(r_var, init.expr2)
                        # print("eq_result: ", eq_result, init.expr2, r_var)
                        if eq_result:
                            is_or = True
                        
                        if isinstance(init.expr2, murphi.VarExpr):
                            cache_is_or = True
                
                if len(init_var) > 0 :
                    for i_var in init_var:
                        # if i_var == str(init.expr2):
                        #     is_or = True
                        eq_result = self.var_Eq_expr(i_var, init.expr2)
                        # print("eq_result: ", eq_result, init.expr2, i_var)
                        if eq_result:
                            is_or = True
                        
                        if isinstance(init.expr2, murphi.VarExpr):
                            # print(init.expr2)
                            cache_is_or = True

                        
            # print("self.arr_idx: ", self.arr_idx)

            init_instance_extra = list()

            str_isin_field = True
            expr_is_var = False

            if is_or:
                for init_tmp in init_instance_tmp:
                    assert isinstance(init_tmp, murphi.OpExpr)
                    # print("init_tmp: ", init_tmp, init_tmp.expr2, type(init_tmp.expr2))
                init_ori_instance = copy.deepcopy(init_instance_tmp)
                # print("init_ori_instance: ", init_ori_instance)
                for init_tmp in init_ori_instance:
                    assert isinstance(init_tmp, murphi.OpExpr)
                    # print("init_tmp: ", init_tmp, init_tmp.expr2, type(init_tmp.expr2))
                    # if count_bra > 1:
                    if not self.expr_is_Var(init_tmp.expr2):
                        # print("init_tmp: ", init_tmp)
                        init_instance_extra.append(init_tmp)
                        init_instance_tmp.remove(init_tmp)
                    
                    letters_list = re.findall(r'\[([a-zA-Z]+)\]', str(init_tmp.expr1))
                    # print("init_tmp: ", init_tmp)
                    for rul_var in ruleset_var:
                        if rul_var in letters_list:
                            str_isin_field = False
                    
                    for ini_var in init_var:
                        if ini_var in letters_list:
                            str_isin_field = False
                    
                    if isinstance(init_tmp.expr1, murphi.VarExpr) & isinstance(init_tmp.expr2, murphi.VarExpr):
                        expr_is_var = True

            # print("init_instance_tmp: ", init_instance_tmp)
            # print("init_instance_extra: ", init_instance_extra)
            # print("str_isin_field: ", str_isin_field)

            init_insextra_dict = dict()

            init_insextra_dict["extra"] = init_instance_extra

            init_instance_rule[f"{startstate_name}"] = init_instance_tmp
            # print("init_instance_rule: ", init_instance_rule)
            
            init_ins_dict = dict()
            if len(ruleset_var_map) > 0:
                init_tmp_dict = dict()
                init_tmp_dict = copy.deepcopy(init_instance_rule)
                if init_insextra_dict:
                    init_tmp_extra = dict()
                    init_tmp_extra = copy.deepcopy(init_insextra_dict)
                for rule_str, rule_item in ruleset_str_dict.items():
                    # print(rule_item, init_tmp_dict, ruleset_var_map)
                    init_tmp_dict = self.get_Ruleset_Ins(rule_item, init_tmp_dict, ruleset_var_map)
                    if init_tmp_extra:
                        init_tmp_extra = self.get_Ruleset_Ins(rule_item, init_tmp_extra, ruleset_var_map)
                
                init_ins_dict = copy.deepcopy(init_tmp_dict)

                # print("init_ins_dict: ", init_ins_dict)
                # print("init_tmp_extra: ", init_tmp_extra)
                
                for key_name, eq_value in init_tmp_dict.items():
                    eq_tmp_list = copy.deepcopy(eq_value)
                    eq_item_list = list()
                    for eq_item in eq_value:
                        assert isinstance(eq_item, murphi.OpExpr)
                        if isinstance(eq_item.expr2, murphi.VarExpr):
                            eq_item_list.append(eq_item)
                    # print("eq_item_list: ", eq_item_list)
                    for var_item in eq_item_list:
                        eq_var_tmp = self.Op_to_Bool(var_item, eq_value)
                        # print("eq_var_tmp: ", eq_var_tmp)
                        if eq_var_tmp:
                            for eq_var in eq_var_tmp:
                                for eq_old in eq_value:
                                    assert isinstance(eq_var, murphi.OpExpr)
                                    assert isinstance(eq_old, murphi.OpExpr)
                                    if eq_var.expr1 == eq_old.expr1:
                                        # print("eq_var.expr1: ", eq_var.expr1)
                                        eq_tmp_list.remove(eq_old)
                                        eq_tmp_list.append(eq_var)
                    init_ins_dict[key_name] = eq_tmp_list

                # print("init_ins_dict: ", init_ins_dict)
            else:
                for var_ins in ruleset_str:
                    for _, num in var_ins.items():
                        ins_sub_list = list()
                        for init_ins in init_instance_rule:
                            init_ins_state = copy.deepcopy(init_ins)
                            ins_sub_state = self.para2ins(init_ins_state, var_ins, ruleset_var_map, [], {})
                            if ins_sub_state not in ins_sub_list:
                                ins_sub_list.append(ins_sub_state)
                        init_ins_dict[f"{startstate_name}_{num}"] = ins_sub_list

                    # print("ins_sub_list: ", ins_sub_list)
            # print("init_ins_dict: ", init_ins_dict)

            # self.all_init_formula = copy.deepcopy(init_sub_instance)

            for _, ins_eq in init_ins_dict.items():
                for eq_expr in ins_eq:
                    self.get_allExpr(eq_expr)
            
            # print("init_tmp_extra: ", init_tmp_extra)
            if init_tmp_extra:
                for _, extra_eq in init_tmp_extra.items():
                    for extra_expr in extra_eq:
                        self.get_allExpr(extra_expr)
            
            # print("self.all_ins_vars: ", self.all_ins_vars)
            # print("protocol_name: ", self.protocol_name)
            self.ins_var_dict[self.protocol_name] = []
            for _, inv_var in self.all_ins_vars.items():
                if inv_var not in self.ins_var_dict[self.protocol_name]:
                    self.ins_var_dict[self.protocol_name].append(inv_var)

            # print("init_sub_instance: ", init_sub_instance)

            # print("init_ins_dict: ", init_ins_dict, len(init_ins_dict))
            union_formula = list()
            union_tmp = list()
            sentinel = None  # 哨兵
            count_name = 0
            init_imp_dict = dict()
            init_ins_dict, init_imp_dict = self.Imply_to_Or(init_ins_dict, init_imp_dict)
            # print("init_imp_dict: ", init_imp_dict)

            all_imply_formula = list()
            for imp_name, imply_list in init_imp_dict.items():
                if imply_list:
                    imply_list = self.eq_isdigit(imply_list)
                    for imp_for in imply_list:
                        deal_formula = None
                        deal_formula = self.deal_OrExpr(imp_for, deal_formula)
                        if str(deal_formula) != "true":
                            # print("deal_formula: ", deal_formula)
                            if deal_formula not in all_imply_formula:
                                all_imply_formula.append(deal_formula)
                            deal_formula = None
            
            if all_imply_formula:
                union_formula.append(self.or_inv(all_imply_formula))

            # print("init_ins_dict: ", init_ins_dict, len(init_ins_dict))
            # print(is_or, str_isin_field, expr_is_var)
            or_sub_formula = list()
            or_count = 0
            for ins_init_name, ins_init_list in init_ins_dict.items():
                if ins_init_list:
                    ins_init_list = self.eq_isdigit(ins_init_list)
                    # print("ins_init_list: ", ins_init_list)
                    # print("ins_init_name: ", ins_init_name)
                    name_list = ins_init_name.split("_")
                    name_len = len(name_list)
                    str_tmp = name_list[0-(name_len - 2)]
                    count_name += 1
                    if name_len > 2:
                        if is_or & (not str_isin_field) & (not expr_is_var):
                            union_sub_formula = self.join_statements(ins_init_list)
                            # print("union_sub_formula: ", union_sub_formula)
                            # print(count_name, len(init_ins_dict), sentinel, str_tmp)
                            if sentinel:
                                if sentinel == str_tmp:
                                    union_tmp.append(union_sub_formula)
                                    if count_name == len(init_ins_dict):
                                        union_formula.append(self.join_statements(union_tmp))
                                        # print("union_formula: ", union_formula)
                                else:
                                    if count_name == len(init_ins_dict):
                                        union_formula.append(self.join_statements(union_tmp))
                                        # print("union_formula: ", union_formula)
                                        union_tmp = list()
                                        union_tmp.append(union_sub_formula)
                                        # print(count_name, len(init_ins_dict), sentinel, str_tmp)
                                        # print("union_tmp: ", union_tmp)
                                        union_formula.append(self.join_statements(union_tmp))
                                        # print("union_formula: ", union_formula)
                                    else:
                                        union_formula.append(self.join_statements(union_tmp))
                                        # print("union_formula: ", union_formula)
                                        union_tmp = list()
                                        union_tmp.append(union_sub_formula)
                                        sentinel = str_tmp
                            else:
                                sentinel = str_tmp
                                union_tmp.append(union_sub_formula)
                                # print("union_tmp: ", union_tmp)
                        else:
                            union_sub_formula = self.join_statements(ins_init_list)
                            # print("union_sub_formula: ", union_sub_formula)
                            sub_formula_tmp = list()
                            sub_formula_tmp.append(union_sub_formula)
                            union_formula.append(self.or_inv(sub_formula_tmp))
                    else:
                        union_sub_formula = self.join_statements(ins_init_list)
                        # print("union_sub_formula: ", union_sub_formula)
                        or_sub_formula.append(union_sub_formula)
                        or_count += 1
                        if expr_is_var:
                            if or_count == len(init_ins_dict):
                                union_formula.append(self.or_inv(or_sub_formula))
                        else:
                            if or_count == len(init_ins_dict):
                                union_formula.append(self.join_statements(or_sub_formula))

            union_no_repeat = list()
            for un_for in union_formula:
                if un_for not in union_no_repeat:
                    union_no_repeat.append(un_for)
            union_formula = union_no_repeat
            # print("union_no_repeat: ", union_no_repeat, len(union_no_repeat))
            # print("union_formula: ", union_formula, len(union_formula))
            # print("init_tmp_extra: ", init_tmp_extra, len(init_tmp_extra))
            init_extra_union = list()
            # print("is_or: ", is_or, "str_isin_field: ", str_isin_field, "cache_is_or: ", cache_is_or)
            if is_or or cache_is_or:
                if init_tmp_extra:
                    for _, init_ext in init_tmp_extra.items():
                        init_extra_union.extend(init_ext)
                    # print("init_extra_union: ", init_extra_union)

                    if init_extra_union:
                        init_extra_union = self.join_statements(init_extra_union)
                        self.init_instance["Init"] = murphi.OpExpr("&", self.or_inv(union_formula), init_extra_union)
                        # print(self.or_inv(union_formula))
                    else:
                        self.init_instance["Init"] = self.or_inv(union_formula)
                else:
                    self.init_instance["Init"] = self.or_inv(union_formula)
            else:
                # print("union_formula: ", union_formula, len(union_formula))
                self.init_instance["Init"] = self.join_statements(union_formula)
            # print(self.init_instance["Init"])
        else:       # 这部分是考虑到没有用ruleset形式，直接使用for循环。。。但这个模块没怎么改，尤其是分布式协议部分，建议还是用ruleset
            start_state_rule = self.prot.start_state
            startstate_name = start_state_rule.name
            for cmd in start_state_rule.cmds:
                # print(cmd, type(cmd))
                init_state, init_var, init_var_map = self.get_sub_init(cmd, init_state, init_var, init_var_map)
            # print(init_state, init_var, init_var_map)
            node_var_list = init_var

            init_value = dict()
            consts_dict = dict()
            for const in self.prot.consts:
                if isinstance(const, murphi.MurphiConstDecl):
                    consts_dict[const.name] = int(str(const.val))
                    # print("const.name: ", const.name, "const.val: ", const.val)

            types_dict = dict()
            for typs in self.prot.types:
                # print("typ: ", typs, type(typs))
                assert isinstance(typs, murphi.MurphiTypeDecl)
                if isinstance(typs.typ, murphi.ScalarSetType):
                    types_dict[typs.name] = typs.typ.const_name
                if isinstance(typs.typ, murphi.RngType):
                    types_dict[typs.name] = typs.typ.upRng

            for init_str, init_typ in init_var_map.items():
                assert isinstance(init_typ, murphi.VarType)
                for consts_str, consts_typ in consts_dict.items():
                    for types_str, types_typ in types_dict.items():
                        if types_typ == consts_str:
                            if init_typ.name == types_str:
                                init_value[init_str] = consts_typ

            # print("init_var: ", init_var)
            init_state_tmp = copy.deepcopy(init_state)
            for init_key, init_val in init_value.items():
                init_node_per, _ = self.get_character(init_val)
                node_str_list = list(itertools.product(copy.deepcopy(init_node_per), repeat = len(init_node_per)))
                node_str = [{key: value for key, value in zip(init_key, combo)} for combo in node_str_list]
                node_str = [dict(t) for t in {tuple(d.items()) for d in node_str}]

                init_state_tmp = self.init_to_ins(init_state_tmp, node_str, init_var_map)

                for init in init_state:
                    arr_tmp = list()
                    if isinstance(init.expr1, murphi.ArrayIndex):
                        # print("init.expr1: ", init.expr1.v, init.expr1.idx, type(init.expr1.v))
                        for init_str, init_val in init_value.items():
                            if isinstance(init.expr1.v, murphi.ArrayIndex):
                                if init_str == str(init.expr1.v.idx):
                                    arr_tmp.append(init_val)
                                if init_str == str(init.expr1.idx):
                                    arr_tmp.append(init_val)
                                if arr_tmp:
                                    self.arr_idx[str(init.expr1.v.v)] = arr_tmp
                            else:
                                if init_str == str(init.expr1.idx):
                                    arr_tmp.append(init_val)
                                if arr_tmp:
                                    self.arr_idx[str(init.expr1.v)] = arr_tmp
                        
            init_sub_instance = copy.deepcopy(init_state_tmp)                
            # print("init_sub_instance: ", init_sub_instance)
            # print("self.arr_idx: ", self.arr_idx)

            for equal in init_sub_instance:
                if isinstance(equal, murphi.OpExpr):
                    if str(equal.expr1) not in self.all_ins_vars:
                        self.all_ins_vars[str(equal.expr1)] = equal.expr1
                    if str(equal.expr1) not in self.all_init_dict:
                        self.all_init_dict[str(equal.expr1)] = equal.expr1
                    if str(equal.expr2) not in self.all_init_dict:
                        self.all_init_dict[str(equal.expr2)] = equal.expr2
            
            self.ins_var_dict[self.protocol_name] = []
            for _, inv_var in self.all_ins_vars.items():
                if inv_var not in self.ins_var_dict[self.protocol_name]:
                    self.ins_var_dict[self.protocol_name].append(inv_var)

            # print("init_sub_instance: ", init_sub_instance)

            init_sub_instance = self.get_Init_for(init_sub_instance)

            # print("init_sub_instance: ", init_sub_instance)
            init_sub_instance = self.eq_isdigit(init_sub_instance)
            
            self.init_instance["Init"] = self.join_statements(init_sub_instance)
            # print(self.init_instance)

    def Imply_to_Or(self, init_ins_dict, init_imp_dict):
        init_ins_tmp = copy.deepcopy(init_ins_dict)
        for ins_name, ins_list in init_ins_tmp.items():
            ins_tmp = copy.deepcopy(ins_list)
            ins_imply = list()
            for ins_formu in ins_list:
                if isinstance(ins_formu, murphi.OpExpr):
                    if ins_formu.op == "->":
                        ins_tmp.remove(ins_formu)
                        ins_imply.append(murphi.OpExpr("|", murphi.NegExpr(ins_formu.expr1), ins_formu.expr2))
            init_ins_dict[ins_name] = ins_tmp
            init_imp_dict[ins_name] = ins_imply
        return init_ins_dict, init_imp_dict

             

    def deal_OrExpr(self, formula, deal_formula):
        if isinstance(formula, murphi.OpExpr):
            if formula.op == "&":
                deal_formula = murphi.OpExpr("&", self.deal_OrExpr(formula.expr1, deal_formula), self.deal_OrExpr(formula.expr2, deal_formula))
            elif formula.op == "|":
                if isinstance(formula.expr2, murphi.BooleanExpr):
                    if str(formula.expr2) == "true":
                        deal_formula = murphi.BooleanExpr(True)
                    elif str(formula.expr2) == "false":
                        deal_formula = formula.expr1
                else:
                    deal_formula = murphi.OpExpr("|", self.deal_OrExpr(formula.expr1, deal_formula), self.deal_OrExpr(formula.expr2, deal_formula))
            else:
                deal_formula = formula
        elif isinstance(formula, murphi.NegExpr):
            deal_formula = murphi.NegExpr(self.deal_OrExpr(formula.expr, deal_formula))
        else:
            deal_formula = formula
        
        return deal_formula


    def init_to_ins(self, init_state_tmp, node_str, init_var_map):
        init_sub_instance = list()
        for init in init_state_tmp:
            # print("init: ", init)
            for var in node_str:
                ini_state = copy.deepcopy(init)
                init_sub_state = self.para2ins(ini_state, var, init_var_map, [], {})
                # print(ini_state, var, init_var_map, init_sub_state, init_sub_state in init_sub_instance)
                if init_sub_state not in init_sub_instance:
                    init_sub_instance.append(init_sub_state)
        return init_sub_instance
   
    def eq_isdigit(self, init_sub_instance):
        for init_sub in init_sub_instance:
            # assert isinstance(init_sub, murphi.OpExpr)
            if isinstance(init_sub, murphi.OpExpr):
                if isinstance(init_sub.expr2, murphi.OpExpr):
                    if init_sub.expr2.op == "=":
                        if isinstance(init_sub.expr2.expr1, murphi.VarExpr) & isinstance(init_sub.expr2.expr2, murphi.VarExpr):
                            if init_sub.expr2.expr1 == init_sub.expr2.expr2:
                                init_sub.expr2 = murphi.BooleanExpr(True)
                            else:
                                init_sub.expr2 = murphi.BooleanExpr(False)

        return init_sub_instance
        
    def get_Ruleset_Ins(self, rule_item, init_tmp_dict, ruleset_var_map):
        init_ins_dict = dict()
        for rule_str in rule_item:
            for str, num in rule_str.items():
                for str_name, init_ins_list in init_tmp_dict.items():
                    ins_sub_list = list()
                    for init_ins in init_ins_list:
                        init_ins_state = copy.deepcopy(init_ins)
                        ins_sub_state = self.para2ins(init_ins_state, rule_str, ruleset_var_map, [], {})
                        if ins_sub_state not in ins_sub_list:
                            ins_sub_list.append(ins_sub_state)
                    init_ins_dict[f"{str_name}_{str}{num}"] = ins_sub_list
        return init_ins_dict

    # init_sub_instance 传入的是实例化后的 init 列表， 这个方法是针对有双重for循环的
    def get_Init_for(self, init_sub_instance):
        init_instance_tmp = copy.deepcopy(init_sub_instance)

        eq_lr_items = list()
        eq_left_items = list()
        for sub_eq in init_instance_tmp:
            # print("sub_eq: ", sub_eq, type(sub_eq))
            if isinstance(sub_eq, murphi.OpExpr):
                # print("sub_eq.expr1: ", sub_eq.expr1, type(sub_eq.expr1))
                if isinstance(sub_eq.expr2, murphi.VarExpr):
                    if re.search(str(sub_eq.expr2), str(sub_eq.expr1)):
                        match_left = sub_eq.expr1
                        equal_items = list()
                        for eq in init_sub_instance:
                            if isinstance(eq, murphi.OpExpr):
                                if match_left == eq.expr1:
                                    equal_items.append(eq)
                        eq_left_items.extend(equal_items)
                        for eq in equal_items:
                            init_sub_instance.remove(eq)
                    if isinstance(sub_eq.expr1, murphi.VarExpr):
                        match_left = sub_eq.expr1
                        equal_items = list()
                        for eq in init_sub_instance:
                            if isinstance(eq, murphi.OpExpr):
                                if match_left == eq.expr1:
                                    equal_items.append(eq)
                        eq_left_items.extend(equal_items)
                        for eq in equal_items:
                            init_sub_instance.remove(eq)
                elif isinstance(sub_eq.expr2, murphi.OpExpr):
                    # if sub_eq.expr2.expr1 != sub_eq.expr2.expr2:
                    #     if f"[{str(sub_eq.expr2.expr1)}]" in str(sub_eq.expr1):
                    if isinstance(sub_eq.expr2.expr1, murphi.VarExpr) & isinstance(sub_eq.expr2.expr2, murphi.VarExpr):
                        # print("sub_eq.expr2.expr2: ", sub_eq.expr2.expr2, type(sub_eq.expr2.expr2))
                        match_right = sub_eq.expr2
                        equal_items = list()
                        for eq in init_sub_instance:
                            if isinstance(eq, murphi.OpExpr):
                                if match_right == eq.expr2:
                                    equal_items.append(eq)
                        eq_lr_items.extend(equal_items)
                        for eq in equal_items:
                            init_sub_instance.remove(eq)

        # print("init_sub_instance: ", init_sub_instance)
        # print("eq_lr_items: ", eq_lr_items)
        # print("eq_left_items: ", eq_left_items)
        eq_right_items = list()

        for sub in eq_left_items:
            if isinstance(sub, murphi.OpExpr):
                match_eq_right = sub.expr2
                equal_right = list()
                for eq_sub in eq_left_items:
                    if isinstance(eq_sub, murphi.OpExpr):
                        if match_eq_right == eq_sub.expr2:
                            equal_right.append(eq_sub)
                if eq_lr_items:
                    eq_settle = self.Op_to_Bool(sub, eq_lr_items)
                    equal_right.append(self.join_statements(eq_settle))
                union_items = self.join_statements(equal_right)
                # print("union_items: ", union_items)
                if union_items not in eq_right_items:
                    eq_right_items.append(union_items)

        # print("eq_right_items: ", eq_right_items)
        if eq_right_items:
            init_sub_instance.append(self.or_inv(eq_right_items))
        return init_sub_instance
    
    def Op_to_Bool(self, equal_Op, equal_list):
        equal_after = list()
        assert isinstance(equal_Op, murphi.OpExpr)
        for equal in equal_list:
            # print("equal: ", equal)
            if isinstance(equal, murphi.OpExpr):
                if isinstance(equal.expr2, murphi.OpExpr) & isinstance(equal.expr1, murphi.ArrayIndex):
                    if equal_Op.expr1 == equal.expr2.expr2:
                        if equal_Op.expr2 == equal.expr2.expr1:
                            # print("equal: ", equal)
                            equal_tmp = murphi.OpExpr(equal.op, equal.expr1, murphi.BooleanExpr(True))
                            # print("equal_tmp: ", equal_tmp)
                            if equal_tmp not in equal_after:
                                equal_after.append(equal_tmp)
                        else:
                            equal_tmp = murphi.OpExpr(equal.op, equal.expr1, murphi.BooleanExpr(False))
                            if equal_tmp not in equal_after:
                                equal_after.append(equal_tmp)
        # print("equal_after: ", equal_after)
        if equal_after:
            equal_new = copy.deepcopy(equal_after)
        else:
            equal_new = None
        # print("equal_new: ", equal_new)
        return equal_new

    def getRules(self):
        sub_rule_ins = dict()
        for name, rule in self.prot.rule_map.items():
            """
            self.prot.rule_map.items()：存储的是协议
            name：是协议名
            rule：是协议内容 
            """
            sub_rule_dict = dict()
            global permutation_type

            # for var: name and type

            if isinstance(rule, murphi.MurphiRuleSet):
                # print("rule.var_map: ", rule.var_map)
                sub_rule_dict["var"] = rule.var_map
                self.rule_var_map[name] = rule.var_map
                # for guard: OpExpr
                sub_rule_dict["guard"] = rule.rule.cond
                # for assignments
                sub_rule_dict["assign"] = rule.rule.cmds
            elif isinstance(rule, murphi.MurphiRule):
                # for guard: OpExpr
                sub_rule_dict["var"] = {}
                self.rule_var_map[name] = {}
                sub_rule_dict["guard"] = rule.cond
                # for assignments
                sub_rule_dict["assign"] = rule.cmds
            self.rule_para[name] = sub_rule_dict
            # for construct instantiated rule vars
            # m:不变式参数个数 的n:规则的参数个数 排列
            inv_name = ""

            sub_var_ins = dict()
            for inv in self.inv_var_length.keys():
                inv_name = inv

                # 实例化

                for var,type in sub_rule_dict["var"].items():
                    assert isinstance(type, murphi.VarType)
                    if isinstance(self.typ_map[type.name], murphi.ScalarSetType):
                        downRng = 1
                        upRng = 1 + const_map[self.typ_map[str(type)].const_name]
                    elif isinstance(self.typ_map[type.name], murphi.RngType):
                        if self.typ_map[str(type)].downRng in const_map.keys():
                            downRng = int(const_map[self.typ_map[str(type)].downRng])
                        else:
                            downRng = int(self.typ_map[str(type)].downRng)
                        if self.typ_map[str(type)].upRng in const_map.keys():
                            upRng = 1 + int(const_map[self.typ_map[str(type)].upRng])
                        else:
                            upRng = 1 + int(self.typ_map[str(type)].upRng)

                    sub_var_ins[var] = [i for i in range(downRng, upRng)]
                    self.arrayVar_insLength[str(type)] = upRng - 1
            
            sub_rule_ins[name] = sub_var_ins
            self.rule_var_ins[inv_name] = sub_rule_ins

        # for inv:all rules
        for inv,rules in self.rule_var_ins.items():
            # print("rules: ", rules)
            rule_vars_dict = dict()
            # for inv-one rule:instantiated rule vars
            for rule, rule_vars in rules.items():

                # for each var
                i = 1

                # itertools.product：类似于求多个可迭代对象的笛卡尔积。
                ins_permutations = list(itertools.product(*rule_vars.values()))
                ins_permutations = [{key: value for key, value in zip(rule_vars.keys(), combo)} for combo in ins_permutations]

                for ins_permutation in ins_permutations:

                    sub_rule_instance_dict = dict()
                    ins_var4rule_list = list()
                    instance_name = inv + "_" + rule + str(i)

                    ins_dict = ins_permutation  # {'i': 1}
                    # for guard
                    guard_dp = copy.deepcopy(self.rule_para[rule]["guard"])

                    guard_vars = []
                    sub_rule_instance_dict["guard"] = self.para2ins(guard_dp, ins_dict, self.rule_var_map[rule], guard_vars, {})
                    for var in guard_vars:
                        if str(var) not in self.all_ins_vars:
                            self.all_ins_vars[str(var)] = var

                    # for assignment
                    sub_assign_list = list()
                    for assignment in self.rule_para[rule]["assign"]:
                        assign_dp = copy.deepcopy(assignment)  # n[i] := T;
                        self.ins_var4rule = list()  # 创建一个空列表
                        if isinstance(assignment, murphi.UndefineCmd):
                            pass
                        else:
                            subassignvars = []
                            assignCmds = self.para2ins(assign_dp, ins_dict, self.rule_var_map[rule], subassignvars, {})
                            for var in subassignvars:
                                if str(var) not in self.all_ins_vars:
                                    self.all_ins_vars[str(var)] = var

                            if isinstance(assignCmds, list):
                                sub_assign_list.extend(assignCmds)
                            else:
                                sub_assign_list.append(assignCmds)
                        if self.ins_var4rule:
                            ins_var4rule_list.extend(self.ins_var4rule)
                    assign_vars = ins_var4rule_list

                    sub_rule_instance_dict["assign"] = sub_assign_list

                    sub_rule_instance_dict["assumption"] = [elem for elem in self.ins_var_dict[inv] if
                                                            elem not in ins_var4rule_list]

                    sub_rule_instance_dict["!inv"] = murphi.NegExpr(self.inv_instance[inv])

                    sub_rule_instance_dict["inv_name"] = inv

                    sub_rule_instance_dict["rule_name"] = rule

                    if self.invHoldForRule2(assign_vars, self.ins_var_dict[inv]):
                        # print("sub_rule_instance_dict: ", sub_rule_instance_dict)
                        self.formula_instances[instance_name] = sub_rule_instance_dict
                        # print("self.formula_instances: ", self.formula_instances)
                    else:
                        self.deduction[instance_name] = sub_rule_instance_dict

                    i += 1

        # 打开文件并写入内容
        # with open(self.parse_name+'_formula.txt', 'w') as file:
        #     file.write("\n\n")
        #     file.write("All parameterized rules:\n")
        #     file.write(str(self.rule_para))
        #     file.write("\n\n")
        #     file.write("All parameterized invariants:\n")
        #     file.write(str(self.inv_para))
        #     file.write("\n\n")
        #     file.write("All instantiated invariants:\n")
        #     file.write(str(self.inv_instance))
        #     file.write("\n\n")
        #     file.write("Invalid F:\n")
        #     file.write(str(self.deduction))
        #     file.write("\n\n")
        #     file.write("Valid F:\n")
        #     # print("self.formula_instances: ", self.formula_instances)
        #     file.write(str(self.formula_instances))
        #     file.write("\n\n")


    def invHoldForRule2(self,assignVars,invVars):
        for invVar in invVars:
            for assignVar in assignVars:
                if invVar == assignVar:
                    return True
        return False

    def getInvVars(self, inv, inv_name, sub_var_dict, sub_inv_dict, sub_array_var):
        if isinstance(inv, murphi.ForallExpr):
            sub_var_dict[inv.var] = inv.typ
            sub_array_var[inv.var] = inv.typ
            # cp_inv_expr = copy.deepcopy(inv.expr)
            # print("cp_inv_expr:",cp_inv_expr)
            # inv = inv.expr
            if isinstance(inv.expr, murphi.ForallExpr):
                # inv.expr = cp_inv_expr.expr
                # print("inv.expr:",inv.expr)
                self.getInvVars(inv.expr, inv_name, sub_var_dict, sub_inv_dict, sub_array_var)
            else:
                self.getInvVars(inv.expr, inv_name, sub_var_dict, sub_inv_dict, sub_array_var)
                sub_inv_dict["invs"] = inv.expr
        elif isinstance(inv, murphi.VarExpr):
            sub_var_dict[inv.name] = inv.typ

        elif isinstance(inv, murphi.OpExpr):
            if isinstance(inv.expr1,murphi.ForallExpr) | isinstance(inv.expr2, murphi.ForallExpr):
                if isinstance(inv.expr1, murphi.ForallExpr):
                    _, half_inv,_ = self.getInvVars(inv.expr1, inv_name, sub_var_dict, sub_inv_dict, sub_array_var)
                    sub_inv_dict["invs"] = murphi.OpExpr(inv.op, half_inv["invs"], inv.expr2)
                elif isinstance(inv.expr1, murphi.OpExpr):
                    self.getInvVars(inv.expr1.expr1, inv_name, sub_var_dict, sub_inv_dict, sub_array_var)
                    self.getInvVars(inv.expr1.expr2, inv_name, sub_var_dict, sub_inv_dict, sub_array_var)
                if isinstance(inv.expr2, murphi.ForallExpr):
                    print("2-forall:",inv.expr2)
                    _, half_inv,_ = self.getInvVars(inv.expr2, inv_name, sub_var_dict, sub_inv_dict, sub_array_var)
                    # print("after:",inv.expr2)
                    # print("half_inv:",half_inv)
                    sub_inv_dict["invs"] = murphi.OpExpr(inv.op, inv.expr1, half_inv["invs"])
                elif isinstance(inv.expr2, murphi.OpExpr):
                    self.getInvVars(inv.expr2.expr1, inv_name, sub_var_dict, sub_inv_dict, sub_array_var)
                    self.getInvVars(inv.expr2.expr2, inv_name, sub_var_dict, sub_inv_dict, sub_array_var)
            else:
                self.getInvVars(inv.expr1, inv_name, sub_var_dict, sub_inv_dict, sub_array_var)
                self.getInvVars(inv.expr2, inv_name, sub_var_dict, sub_inv_dict, sub_array_var)

            # sub_inv_dict["invs"] = inv

        elif isinstance(inv, murphi.NegExpr):
            self.getInvVars(inv.expr, inv_name, sub_var_dict, sub_inv_dict, sub_array_var)

        return sub_var_dict, sub_inv_dict, sub_array_var

    # 因为传入的是实例化好的 deadlcok 公式，故需要重写 getInv
    def getInv_2(self):
        inv_name = ''

        if self.invariant_ins:
            pass
        else:
            self.invariant_ins[self.protocol_name] = None
        
        for key in self.invariant_ins.keys():
            inv_name = key
        # print("inv_name: ", inv_name)
        inv = self.invariant_ins[self.protocol_name]
        # print("inv: ", inv)
        # 带参形式的实例化

        sub_var_dict, sub_inv_dict, sub_array_var = self.getInvVars(inv, inv_name, {}, {}, {})

        # print("sub_array_var: ", sub_array_var)

        for key,value in self.rule_var_list.items():
            self.all_rule_dict[key] = value
        for key,value in sub_var_dict.items():
            self.all_rule_dict[key] = value
        # print("self.all_rule_dict: ", self.all_rule_dict)
        self.rule_dl_map[inv_name] = self.all_rule_dict

        self.inv_array_var_map[inv_name] = self.rule_var_list
        self.inv_var_map = self.rule_dl_map
        self.inv_var_length[inv_name] = len(self.all_rule_dict)
        # print("self.inv_var_map: ", self.inv_var_map)
        # print("self.inv_var_length: ", self.inv_var_length)


        self.ins_var = None
        # print("inv: ", inv)

        self.inv_instance[inv_name] = self.para2ins(inv, {}, {},
                                                    [], self.inv_var_map[inv_name], True)
        
        # print("self.ins_var: ", self.ins_var)
        # print("self.ins_var_dict: ", self.ins_var_dict)
        if not self.ins_var == None:
            ins_var = copy.deepcopy(self.ins_var)
            # print("ins_var: ", ins_var)
            if ins_var:
                for var in ins_var:
                    # print("var: ", var)
                    if str(var) not in self.all_ins_vars.keys():
                        self.all_ins_vars[str(var)] = var
            self.ins_var_dict[inv_name] = ins_var
        
        for var in self.all_ins_vars:
            if self.all_ins_vars[var] not in self.ins_var_dict[inv_name]:
                self.ins_var_dict[inv_name].append(self.all_ins_vars[var])
        # print("self.ins_var: ", self.ins_var)
        # print("self.ins_var_dict: ", self.ins_var_dict)
        # print("self.all_ins_vars: ", self.all_ins_vars)

        self.getRules()

    def getInvs(self):
        inv_name = ""
        for inv in self.prot.inv_map.values():
            inv_name = inv.name
            # print("inv_name:",inv_name)
            assert isinstance(inv, MurphiInvariant)
            # print("inv.inv:",inv.inv)
            # for var: name and type
            sub_var_dict, sub_inv_dict, sub_array_var = self.getInvVars(inv.inv, inv_name, {}, {}, {})
            sub_inv_dict["var"] = sub_var_dict
            self.inv_var_map[inv_name] = sub_var_dict
            self.inv_array_var_map[inv_name] = sub_array_var
            self.inv_var_length[inv_name] = len(sub_var_dict)
            # print("self.inv_var_map:", self.inv_var_map)
            # print("self.inv_array_var_map:",self.inv_array_var_map)
            self.inv_para[inv_name] = sub_inv_dict
            # print("self.inv_para:", self.inv_para)


        # instances for parameters
            inv_insNum = 1
            sub_insVar = dict()
            # 带参形式的实例化
            for var in sub_array_var.keys():
                sub_insVar[var] = inv_insNum
                inv_insNum +=1
            self.inv_var_ins[inv_name] = sub_insVar
            # print(self.inv_var_ins)
            # print(self.inv_para[inv_name]["invs"], self.inv_var_ins[inv_name])
            dp = copy.deepcopy(self.inv_para[inv_name]["invs"])
            # print(dp)
            self.ins_var = None
            self.inv_instance[inv_name] = self.para2ins(dp, self.inv_var_ins[inv_name],self.inv_array_var_map[inv_name],[],self.inv_var_map[inv_name],True)

            # print("self.inv_instance:",self.inv_instance)
            if not self.ins_var==None:
                ins_var = copy.deepcopy(self.ins_var)
                if ins_var:
                    for var in ins_var:
                        if str(var) not in self.all_ins_vars.keys():
                            self.all_ins_vars[str(var)] = var
                self.ins_var_dict[inv_name] = ins_var
            # print(self.inv_para[inv_name]["invs"],self.inv_var_ins[inv_name])
            # {'mutualEx': OpExpr(->, 1 != 2, n[1] = C ->   n[2] != C)}
            # print("self.ins_var_dict:", self.ins_var_dict)
            self.getRules()
      
    def or_inv(self,statement):
        if len(statement) == 1:
            return statement[0]
        else:
            return murphi.OpExpr('|', statement[-1], self.or_inv(statement[:-1]))

    # 获取实例化后的 deadlock 公式
    def getDlInv(self):
        dl_name = [self.dl_inv_name]
        guard_formula = list()
        sub_rule_ins = dict()
        for name, rule in self.prot.rule_map.items():
            """
            self.prot.rule_map.items()：存储的是协议
            name：是协议名
            rule：是协议内容 
            """
            sub_rule_dict = dict()
            global permutation_type

            # for var: name and type
            if isinstance(rule, murphi.MurphiRuleSet):
                sub_rule_dict["var"] = rule.var_map
                self.rule_var_map[name] = rule.var_map
                # for guard: OpExpr
                sub_rule_dict["guard"] = rule.rule.cond
                # for assignments
                sub_rule_dict["assign"] = rule.rule.cmds
            elif isinstance(rule, murphi.MurphiRule):
                # for guard: OpExpr
                sub_rule_dict["var"] = {}
                self.rule_var_map[name] = {}
                sub_rule_dict["guard"] = rule.cond
                # for assignments
                sub_rule_dict["assign"] = rule.cmds
            self.rule_para[name] = sub_rule_dict
            # print(self.rule_para)
            # for construct instantiated rule vars
            # m:不变式参数个数 的n:规则的参数个数 排列
            # print("self.inv_var_map:",self.inv_var_map, self.inv_var_length)
            inv_name = ""

            sub_var_ins = dict()

            for inv in dl_name:
                inv_name = inv

                # 实例化
                for var,type in sub_rule_dict["var"].items():
                    assert isinstance(type, murphi.VarType)
                    if isinstance(self.typ_map[type.name], murphi.ScalarSetType):
                        downRng = 1
                        upRng = 1 + const_map[self.typ_map[str(type)].const_name]
                    elif isinstance(self.typ_map[type.name], murphi.RngType):
                        if self.typ_map[str(type)].downRng in const_map.keys():
                            downRng = int(const_map[self.typ_map[str(type)].downRng])
                        else:
                            downRng = int(self.typ_map[str(type)].downRng)
                        if self.typ_map[str(type)].upRng in const_map.keys():
                            upRng = 1 + int(const_map[self.typ_map[str(type)].upRng])
                        else:
                            upRng = 1 + int(self.typ_map[str(type)].upRng)

                    sub_var_ins[var] = [i for i in range(downRng, upRng)]
                    # var_maxConstNum = murphi.const_map[murphi.digitType_map[str(type)]]
                    # sub_var_ins[var] = [i for i in range(1, var_maxConstNum+1)]

                    self.arrayVar_insLength[str(type)] = upRng - 1

            sub_rule_ins[name] = sub_var_ins
            self.rule_var_ins[inv_name] = sub_rule_ins

        # for inv:all rules
        for inv, rules in self.rule_var_ins.items():
            rule_vars_dict = dict()
            # for inv-one rule:instantiated rule vars
            for rule, rule_vars in rules.items():
                # for each var
                i = 1

                # 获取变量 ℹ 和 j
                if len(self.rule_var_map) == len(rules):
                    for key,value in self.rule_var_map.items():
                        for m,n in value.items():
                            if m not in self.rule_var_list.keys():
                                self.rule_var_list[m] = n

                # print(len(self.rule_var_map), len(rules))


                ins_permutations = list(itertools.product(*rule_vars.values()))
                ins_permutations = [{key: value for key, value in zip(rule_vars.keys(), combo)} for combo in
                                    ins_permutations]

                # print("ins_permutations: ", ins_permutations)
                for ins_permutation in ins_permutations:
                    sub_rule_instance_dict = dict()
                    ins_var4rule_list = list()
                    instance_name = inv + "_" + rule + str(i)

                    ins_dict = ins_permutation  # {'i': 1}
                    # for guard
                    guard_dp = copy.deepcopy(self.rule_para[rule]["guard"])
                    guard_vars = []
                    sub_rule_instance_dict["guard"] = self.para2ins(guard_dp, ins_dict, self.rule_var_map[rule], guard_vars, {})
                    for var in guard_vars:
                        if str(var) not in self.all_ins_vars:
                            self.all_ins_vars[str(var)] = var

                    guard_formula.append(sub_rule_instance_dict["guard"])

                    i += 1

        # 如果需要的是死锁不变式，对 guard 进行处理
        neg_guard = list()
        for sub_for in guard_formula:
            neg_guard.append(murphi.NegExpr(sub_for))

        self.all_guard = self.join_statements(neg_guard)
        self.invariant_ins[self.dl_inv_name] = self.all_guard
        # print("self.invariant_ins: ", self.invariant_ins)
        # print(self.all_guard)

        self.getInv_2()

    def get_guard(self, guard_list):
        guard_var = list()
        for guard in guard_list:
            guard_str = list()
            if isinstance(guard, list):
                guard_var.extend(self.get_guard(guard))
            elif isinstance(guard, AssignCmd):
                if isinstance(guard.expr, EnumValExpr):
                    for key, value in self.key_enum.items():
                        if value[0] == guard.expr.enum_type:
                            cmd = murphi.OpExpr('=', guard.var, value[1])
                            # print("cmd: ", cmd)
                            if cmd not in guard_var:
                                guard_var.append(cmd)
            elif isinstance(guard, murphi.OpExpr):
                if guard.op == '&':
                    guard_str.append(guard.expr1)
                    guard_str.append(guard.expr2)
                    guard_var.extend(self.get_guard(guard_str))
                elif guard.op == '=':
                    if isinstance(guard.expr2, murphi.BooleanExpr):
                        tmp1 = murphi.OpExpr('=', guard.expr1, murphi.BooleanExpr(False))
                        tmp2 = murphi.OpExpr('=', guard.expr1, murphi.BooleanExpr(True))
                        if tmp1 not in guard_var:
                            guard_var.append(tmp1)
                        if tmp2 not in guard_var:
                            guard_var.append(tmp2)
                    else:
                        if guard not in guard_var:
                            guard_var.append(guard)
                elif guard.op == '|':
                    guard_str.append(guard.expr1)
                    guard_str.append(guard.expr2)
                    guard_var.extend(self.get_guard(guard_str))
        # print("guard_var: ", guard_var)
        return guard_var

    def replace_letters_with_numbers(self, formula):
        letter_dict = {}
        letter_counter = 0

        def replace(match):
            nonlocal letter_counter
            letter = match.group(1)
            if letter not in letter_dict:
                letter_dict[letter] = str(letter_counter + 1)
                letter_counter += 1
            return "[" + letter_dict[letter] + "]"

        pattern = re.compile(r'\[([A-Za-z])\]')
        replaced_formula = pattern.sub(replace, formula)

        return replaced_formula

    def del_repeat_formula(self, formula_list):
        del_list = list()
        for formula in formula_list:
            if formula not in del_list:
                del_list.append(formula)
        return del_list

    def get_noeq_list(self, eq_list):
        noeq_list = list()
        for eq in eq_list:
            if isinstance(eq, murphi.OpExpr):
                noeq = murphi.OpExpr("!=", eq.expr1, eq.expr2)
            if noeq not in noeq_list:
                noeq_list.append(noeq)
        return noeq_list

    # 处理公式的函数
    def process_formula(self, formula):
        # 去掉前后的!()
        formula = formula[2:-1]
        # 用&分割
        equations = [eq.strip() for eq in formula.split('&')]
        return equations
    
    def inv_op(self, sub_list, var_dict):
        print("sub_list, var_dict : ", sub_list, var_dict)
        for key, value in var_dict.items():
            if key.lower() == sub_list[0].lower():
                expr1 = value
            if key.lower() == sub_list[1].lower():
                expr2 = value
        deal_formula = murphi.OpExpr(sub_list[2], expr1, expr2)
        return deal_formula

    def replace_letters_with_dict(self, expr, replace_dict):
        pattern = re.compile(r'\[([a-zA-Z])\]')
        expr_split = expr.replace("!(", "").replace(")", "").split("&")
        # print("expr_split: ",expr_split)
        
        all_var_dict = dict()
        letter_counter = 1
        eq_var_dict = dict()
        eq_new_list = list()
        for eq in expr_split:
            eq_new = copy.deepcopy(eq)
            matches = pattern.findall(eq)
            if matches:
                for re_str, re_idx in replace_dict.items():
                    eq_idx_dict = dict()
                    if re_str in eq:
                        for idx in range(len(re_idx)): 
                            # print("matches[idx]: ", matches[idx])
                            if matches[idx] not in all_var_dict:
                                letter_str = self.str_is_exist(matches[idx], re_str, eq_var_dict, idx)
                                # print("letter_str: ", letter_str)
                                if letter_str:
                                    letter_counter = int(letter_str) + 1
                                # print("letter_counter: ", letter_counter)
                                if letter_counter <= re_idx[idx]:
                                    eq_new = eq_new.replace(f"[{matches[idx]}]", f"[{str(letter_counter)}]")
                                    all_var_dict[matches[idx]] = str(letter_counter)
                                    eq_idx_dict[matches[idx]] = str(letter_counter)
                                else:
                                    letter_counter = 1
                                    eq_new = eq_new.replace(f"[{matches[idx]}]", f"[{str(letter_counter)}]")
                                    all_var_dict[matches[idx]] = str(letter_counter)
                                    eq_idx_dict[matches[idx]] = str(letter_counter)

                            else:
                                eq_new = eq_new.replace(f"[{matches[idx]}]", f"[{all_var_dict[matches[idx]]}]")
                                eq_idx_dict[matches[idx]] = f"{all_var_dict[matches[idx]]}"
                    if eq_idx_dict:
                        # eq_var_list.append(eq_idx_dict)
                        eq_var_dict[re_str] = eq_idx_dict
                eq_new_list.append(eq_new)
                # print("eq_var_dict: ",eq_var_dict)
                # print("eq_new: ", eq_new)
            else:
                eq_new_list.append(eq)
        
        result = "!(" + "&".join(eq_new_list) + ")"
        # print("result: ", result)
        return result

    def str_is_exist(self, str, str_name, str_dict, idx):
        # print(str, str_name, str_dict)
        if str_dict:
            for str_key, str_val in str_dict.items():
                count = 0
                if str_name == str_key:
                    for str_val_key, str_val_val in str_val.items():
                        if count == int(idx):
                            if str != str_val_key:
                                return str_val_val
                        count += 1
        return None

    def get_str_Inv(self):
        all_sub_causality = dict()
        for var, typ in self.prot.typ_map.items():
            if isinstance(typ, murphi.EnumType):
                for sub_typ in typ.names:
                    all_sub_causality[str(sub_typ)] = murphi.EnumValExpr(typ, sub_typ)
        all_sub_causality["false"] = murphi.BooleanExpr(False)
        all_sub_causality["true"] = murphi.BooleanExpr(True)

        # print("self.all_ins_vars: ", self.all_ins_vars, len(self.all_ins_vars))
        for key, value in self.all_ins_vars.items():
            if key not in self.all_init_dict:
                self.all_init_dict[key] = value
        for key, value in all_sub_causality.items():
            if key not in self.all_init_dict:
                self.all_init_dict[key] = value
        # print("self.all_init_dict: ", self.all_init_dict)

        # self.dl_inv = self.replace_letters_with_numbers(self.dl_inv.replace(";", ""))
        if self.dl_inv:
            if isinstance(self.dl_inv, murphi.NegExpr) or isinstance(self.dl_inv, murphi.OpExpr):
                self.invariant_ins[self.dl_inv_name] = self.dl_inv

            else:
                self.dl_inv = self.replace_letters_with_dict(self.dl_inv.replace(";", ""), self.arr_idx)
                # print(self.dl_inv)


                deal_inv = self.process_formula(self.dl_inv.strip())
                # print("deal_inv: ", deal_inv)
                all_deal_inv = list()
                for sub_inv in deal_inv:
                    if "!=" in sub_inv:
                        deal_noeq_inv = [eq.strip() for eq in sub_inv.split("!=")]
                        deal_noeq_inv.append("!=")
                        all_deal_inv.append(self.inv_op(deal_noeq_inv, self.all_init_dict))
                    elif "=" in sub_inv:
                        deal_eq_inv = [eq.strip() for eq in sub_inv.split("=")]
                        deal_eq_inv.append("=")
                        # print(deal_eq_inv)
                        all_deal_inv.append(self.inv_op(deal_eq_inv, self.all_init_dict))
                # print("all_deal_inv: ", all_deal_inv)
                self.inv_init_smt = self.join_statements(all_deal_inv)

                self.all_guard = murphi.NegExpr(self.inv_init_smt)

                self.invariant_ins[self.dl_inv_name] = self.all_guard
            print("invariant_ins: ", self.invariant_ins)
        self.getInv_2()


    # exists 要和 forall 分开处理
    def get_Axiom_items(self, decl, forall_axiom_var, forall_axiom_var_typ, axiom_formula, axiom_name, exists_axiom_var, exists_axiom_var_typ):
        if isinstance(decl, murphi.AxiomExpr):
            # print("decl: ", decl.name, decl.expr, type(decl.expr))
            axiom_name = str(decl.name.value).replace("\"", "")
            self.get_Axiom_items(decl.expr, forall_axiom_var, forall_axiom_var_typ, axiom_formula, axiom_name, exists_axiom_var, exists_axiom_var_typ)
        elif isinstance(decl, murphi.NegExpr):
            # print("decl.expr: ", decl.expr.expr, type(decl.expr.expr))
            self.get_Axiom_items(decl.expr, forall_axiom_var, forall_axiom_var_typ, axiom_formula, axiom_name, exists_axiom_var, exists_axiom_var_typ)
                
        elif isinstance(decl, murphi.ForallExpr):
            # print("decl.expr.expr: ", decl.expr, type(decl.expr))
            forall_axiom_var.append(decl.var)
            forall_axiom_var_typ[decl.var] = decl.typ
            if isinstance(decl.expr, murphi.NegExpr) | isinstance(decl.expr, murphi.OpExpr):
                axiom_formula.append(decl.expr)
            self.get_Axiom_items(decl.expr, forall_axiom_var, forall_axiom_var_typ, axiom_formula, axiom_name, exists_axiom_var, exists_axiom_var_typ)
        
        elif isinstance(decl, murphi.ExistsExpr):
            exists_axiom_var.append(decl.var)
            exists_axiom_var_typ[decl.var] = decl.typ
            if isinstance(decl.expr, murphi.NegExpr) | isinstance(decl.expr, murphi.OpExpr):
                axiom_formula.append(decl.expr)
            self.get_Axiom_items(decl.expr, forall_axiom_var, forall_axiom_var_typ, axiom_formula, axiom_name, exists_axiom_var, exists_axiom_var_typ)
        
        return forall_axiom_var, forall_axiom_var_typ, axiom_formula, axiom_name, exists_axiom_var, exists_axiom_var_typ
        

    def get_Axiom(self):
        # print(self.prot.decls)
        axiom_ins_list = list()
        for decl in self.prot.decls:
            forall_axiom_var = list()
            forall_axiom_typ_map = dict()
            axiom_formula = list()
            axiom_name = None
            exists_axiom_var = list()
            exists_axiom_typ_map = dict()
            forall_axiom_var, forall_axiom_typ_map, axiom_formula, axiom_name, exists_axiom_var, exists_axiom_typ_map = self.get_Axiom_items(decl, forall_axiom_var, forall_axiom_typ_map, axiom_formula, axiom_name, exists_axiom_var, exists_axiom_typ_map)
            if isinstance(decl, murphi.AxiomExpr):
                # print("decl: ", decl)
                axiom_formula = self.deal_imply(axiom_formula)
                axiom_ins_tmp = self.axiom_deal_EORF(forall_axiom_var, forall_axiom_typ_map, axiom_formula, exists_axiom_var, exists_axiom_typ_map)
                # print("axiom_ins_tmp: ", axiom_ins_tmp)
                axiom_ins_list.append(axiom_ins_tmp)
        if axiom_ins_list:
            self.axiom_instance["axiom"] = self.join_statements(axiom_ins_list)

        # print(self.axiom_instance)
    
    def deal_imply(self, formula_list):
        new_formula_list = list()
        for forl in formula_list:
            for_tmp = None
            assert isinstance(forl, murphi.OpExpr)
            if forl.op == "->":
                for_tmp = murphi.OpExpr("|", murphi.NegExpr(forl.expr1), forl.expr2)
            if for_tmp:
                new_formula_list.append(for_tmp)
            else:
                new_formula_list.append(forl)
        return new_formula_list

        
    def axiom_deal_EORF(self, forall_axiom_var, forall_axiom_typ_map, axiom_formula, exists_axiom_var, exists_axiom_typ_map):
        axiom_ins_tmp = None
        # print("axiom_typ_map: ", axiom_typ_map)
        if forall_axiom_var:   
            forall_typ_count = self.get_var_count(forall_axiom_typ_map)
            # print("forall_typ_count: ", forall_typ_count)

            forall_axiom_list = copy.deepcopy(axiom_formula)

            for tn, tc in forall_typ_count.items():
                forall_axiom_list = self.axiom_to_instance(forall_axiom_list, tn, tc, forall_axiom_typ_map)
                

        if exists_axiom_var:
            exists_typ_count = self.get_var_count(exists_axiom_typ_map)
            # print("exists_typ_count: ", exists_typ_count)

            exists_axiom_list = list()
            exists_axiom_list.append(copy.deepcopy(self.join_statements(forall_axiom_list)))

            for el_na, el_co in exists_typ_count.items():
                exists_axiom_list = self.axiom_to_instance(exists_axiom_list, el_na, el_co, exists_axiom_typ_map)
            
            # print("exists_axiom_list: ", exists_axiom_list, len(exists_axiom_list))
            for ex_formula in exists_axiom_list:
                self.get_allExpr(ex_formula)
            
            # print("self.all_ins_vars: ", self.all_ins_vars)

            axiom_ins_tmp = self.or_inv(exists_axiom_list)
            
        else:
            
            # print("forall_axiom_list: ", forall_axiom_list)
            forall_axiom_list = self.eq_isdigit(forall_axiom_list)
            forall_axiom_deal = list()
            for for_ax in forall_axiom_list:
                forax_tmp = None
                forax_tmp = self.deal_OrExpr(for_ax, forax_tmp)
                if forax_tmp not in forall_axiom_deal:
                    forall_axiom_deal.append(forax_tmp)
                # print("forax_tmp: ", forax_tmp)
            # print("forall_axiom_deal: ", forall_axiom_deal)
            
            for for_formula in forall_axiom_deal:
                self.get_allExpr(for_formula)
            
            axiom_ins_tmp = self.join_statements(forall_axiom_deal)
        return axiom_ins_tmp
        
    def get_var_count(self, axiom_typ_map):
        axiom_typ_name = dict()
        for typ in self.prot.types:
            assert isinstance(typ, murphi.MurphiTypeDecl)
            if isinstance(typ.typ, murphi.ScalarSetType):
                for var_name, axiom_typ in axiom_typ_map.items():
                    if isinstance(axiom_typ, murphi.VarType):
                        if str(typ.name) == str(axiom_typ.name):
                            axiom_typ_name[var_name] = typ.typ.const_name

        axiom_typ_count = dict()
        const_map = dict()

        for const in self.prot.consts:
            assert isinstance(const, murphi.MurphiConstDecl)
            const_map[const.name] = int(const.val)

        for typ_name, typ_type in axiom_typ_name.items():
            for const_name, const_count in const_map.items():
                if str(typ_type) == str(const_name):
                    axiom_typ_count[typ_name] = const_count
        
        return axiom_typ_count

    
    def axiom_to_instance(self, axiom_list, tn, tc, axiom_typ_map):
        typ_dict = dict()
        axiom_tmp_list = list()
        for ax_for in axiom_list:
            for typ_count in range(1, int(tc)+1):
                axiom_tmp = copy.deepcopy(ax_for) 
                typ_dict[tn] = typ_count
                axiom_tmp_list.append(self.para2ins(axiom_tmp, typ_dict, axiom_typ_map, [], {}))
        return axiom_tmp_list

            


        
        


if __name__ == "__main__":
    # parse_name = "../protocols/mutualEx/mutualEx"
    # parse_name = "protocols/mutdata/mutdata"
    # parse_name = "../protocols/german/german"
    # parse_name = "../protocols/german_withdata/german"
    # parse_name = "../protocols/german_withoutData/german_withoutData"
    # parse_name = "../protocols/flash_withoutData/flash_nodata_cub"
    # parse_name = "../protocols/flash_withData/flash_data_cub"
    parse_name = "../protocols/philosopher/philosopher_dl"

    # parse_name = "../protocols/decentralized_lock/decentralized_lock"
    # parse_name = "../protocols/Ricart-Agrawala/Ricart-Agrawala"
    # parse_name = "../protocols/lock_server/lock_server"
    # parse_name = "../protocols/shard/shard"
    # parse_name = "../protocols/two_phase_commit/two_phase_commit"
    # parse_name = "../protocols/consensus/consensus"
    # parse_name = "../protocols/paxos/paxos_bmc"

    # GetSMTformula(parse_name=parse_name, node_permutations=[1, 2]).getInvs()
    # print("-----------------------------------------------------------------------------------")

    # filename = '_dl_invs.txt'  # Replace with the actual file name
    # start_string = "start"
    # end_string = "end"
    
    # # Function to check if a line contains "start"
    # def check_for_start(line):
    #     return start_string in line
    
    # # Function to check if a line contains "end"
    # def check_for_end(line):
    #     return end_string in line
    
    # # Continuously read the file line by line and print each line (excluding "start")
    # try:
    #     with open(parse_name + filename, 'r') as file:
    #         for line in file:
    #             if check_for_end(line):
    #                 print("Found 'end' in the file. Breaking the loop.")
    #                 break
    #             elif not check_for_start(line):
    #                 GetSMTformula(parse_name=parse_name, node_permutations=[1, 2], node_list=['i', 'j'], dl_inv=str(line)).dl_smt_solver()
    # except FileNotFoundError:
    #     # Handle the case where the file doesn't exist yet
    #     print("File doesn't exist")

    # inv = "!(n[1] = I & x = false)"
    inv = "!(Cache[2].State = E & Cache[1].State = E)"
    # inv = "!(ShrSet[1] = false & Cache[1].State = E & CurPtr = 1)"
    # inv = "!(Cache[2].Data = 1 & Cache[1].Data = 1 & AuxData = 1 & MemData = 1 & Cache[1].State = I & Cache[2].State = E & Chan2[1].Data = 1 & Chan2[1].Cmd = GntE)"
    # inv = "!(Chan3[1].Data = 2 & ExGntd = true & CurCmd = reqs & Chan3[1].Cmd = invack)"
    # inv = "!(Chan2[i].Data != MemData & Chan2[i].Cmd = GntS)"
    # inv = "!(Sta.NakcMsg.Cmd = NAKC_None & Sta.HomeProc.ProcCmd = NODE_None & Sta.CurrData = 2)"

    # inv = "!(has_lock[i] = true & has_lock[j] = true)"  # decentralized_lock
    # inv = "!(has_lock[1] = false & has_lock[2] = false)"

    # inv = "!(holds[i] = true & holds[j] = true)"   # Ricart-Agrawala
    
    # inv = "!(link[i][k] = true & link[j][k] = true)"   # lock_server

    # inv = "!(owner[1][1] = true & owner[2][1] = true)"  # shard

    # inv = "!(decide_abort[2] = true & go_commit[1] = true);"  # two_phase_commit

    # inv = "!(decided[2][2][1] = true & leader[1][1] = true)"  # consensus
    # inv = "!(member[1][1] = false & member[2][1] = false & member[3][1] = false)"

    # inv = "!(decision[1][1][1] = true & decision[1][1][2] = true)"

    protocol_name = parse_name.split("/")[-1]
    node_number = 2
    # c = GetSMTformula(protocol_name, parse_name=parse_name, dl_inv=str(inv))
    # c.getInit()
    # c.get_Axiom()
    # c.get_str_Inv()
    # c.getDlInv()

    c = GetSMTformula(protocol_name, parse_name=parse_name, dl_inv=None)
    c.getDlInv()
           
    # c.getInvs()
    # print("c.all_ins_vars: ", c.all_ins_vars)

    # c = GetSMTformula(parse_name=parse_name, node_permutations=[1], node_list=['i'], dl_inv=[])
    # c.getInvs()
    # print("c.all_ins_vars", c.all_ins_vars)



