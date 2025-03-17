import socket
from murphiparser import *
import threading
import time
import re

class EmptyException(Exception):
    pass

class ServerException(Exception):
    pass


class RequestType:
    ERROR = -2
    WAITING = -1
    OK = 0
    COMPUTE_REACHABLE = 1
    QUERY_REACHABLE = 2
    CHECK_INV = 3
    SMV_QUIT = 7
    GO_BMC = 10
    CHECK_INV_BMC = 11
    SMV_BMC_QUIT = 12
    SET_SMT2_CONTEXT = 4
    QUERY_SMT2 = 5
    QUERY_STAND_SMT2 = 6
    SET_MU_CONTEXT = 8
    CHECK_INV_BY_MU = 9

def request_type_to_str(rt):
    if rt == RequestType.ERROR:
        return "-2"
    elif rt == RequestType.WAITING:
        return "-1"
    elif rt == RequestType.OK:
        return "0"
    elif rt == RequestType.COMPUTE_REACHABLE:
        return "1"
    elif rt == RequestType.QUERY_REACHABLE:
        return "2"
    elif rt == RequestType.CHECK_INV:
        return "3"
    elif rt == RequestType.SMV_QUIT:
        return "7"
    elif rt == RequestType.GO_BMC:
        return "10"
    elif rt == RequestType.CHECK_INV_BMC:
        return "11"
    elif rt == RequestType.SMV_BMC_QUIT:
        return "12"
    elif rt == RequestType.SET_SMT2_CONTEXT:
        return "4"
    elif rt == RequestType.QUERY_SMT2:
        return "5"
    elif rt == RequestType.QUERY_STAND_SMT2:
        return "6"
    elif rt == RequestType.SET_MU_CONTEXT:
        return "8"
    elif rt == RequestType.CHECK_INV_BY_MU:
        return "9"

def str_to_request_type(s):
    if s == "-2":
        return RequestType.ERROR
    elif s == "-1":
        return RequestType.WAITING
    elif s == "0":
        return RequestType.OK
    elif s == "1":
        return RequestType.COMPUTE_REACHABLE
    elif s == "2":
        return RequestType.QUERY_REACHABLE
    elif s == "3":
        return RequestType.CHECK_INV
    elif s == "7":
        return RequestType.SMV_QUIT
    elif s == "10":
        return RequestType.GO_BMC
    elif s == "11":
        return RequestType.CHECK_INV_BMC
    elif s == "12":
        return RequestType.SMV_BMC_QUIT
    elif s == "4":
        return RequestType.SET_SMT2_CONTEXT
    elif s == "5":
        return RequestType.QUERY_SMT2
    elif s == "6":
        return RequestType.QUERY_STAND_SMT2
    elif s == "8":
        return RequestType.SET_MU_CONTEXT
    elif s == "9":
        return RequestType.CHECK_INV_BY_MU
    else:
        raise Exception("error return code from server: " + s)


# 创建套接字并连接server、接收响应
def make_request(data, host, port):
    sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    # sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
    sock.connect((host, port))
    sock.send(data.encode())
    response = sock.recv(1024).decode()
    sock.close()
    return response


command_id = [0]

# 构建请求并处理响应消息
def request(cmd, req_str, host, port):
    cmd_str = request_type_to_str(cmd)
    cmd_id = command_id[0]
    req = f"{cmd_str},{cmd_id},{req_str}"
    wrapped = f"{len(req)},{req}"

    # 确保id的唯一性
    command_id[0] += 1

    response = make_request(wrapped, host, port)
    res = response.split(',')

    if not res:
        raise EmptyException()

    status = res[0]
    res_data = res[1:]

    s = str_to_request_type(status)
    if s == RequestType.ERROR:
        raise ServerException()
    else:
        return s, res_data


class Smv:
    class CannotCheck(Exception):
        pass

    host = '192.168.1.34'
    port = 50005

    @staticmethod
    def compute_reachable(name, content, smv_ord=""):
        status, _ = request(RequestType.COMPUTE_REACHABLE, f"{name},{content},{smv_ord}", Smv.host, Smv.port)
        return status == RequestType.OK

    @staticmethod
    def query_reachable(name):
        status, diameter = request(RequestType.QUERY_REACHABLE, name, Smv.host, Smv.port)
        if status == RequestType.OK:
            if diameter == ["-1"]:
                raise ServerException()
            else:
                try:
                    return int(diameter[0])
                except ValueError:
                    raise ServerException()
        else:
            return 0

    @staticmethod
    def check_inv(name, inv):
        status, res = request(RequestType.CHECK_INV, f"{name},{inv}", Smv.host, Smv.port)
        if status == RequestType.OK:
            if res == ["0"]:
                raise Smv.CannotCheck()
            else:
                try:
                    return False if res[0].lower() == "false" else True
                except ValueError:
                    raise ServerException()
        else:
            raise ServerException()

    @staticmethod
    def quit(name):
        status, _ = request(RequestType.SMV_QUIT, name, Smv.host, Smv.port)
        return status == RequestType.OK



protocol_name = ""
table = {}

# 根据提供的协议，执行NuSMV计算可达集compute_reachable，并等待查询结果query_reachable
# def set_context(name, smv_file_content, smv_ord=""):
#     global protocol_name
#     protocol_name = name
#     _res = Smv.compute_reachable(name, smv_file_content, smv_ord)
#     diameter = 0
#     while diameter == 0:
#         import time
#         time.sleep(1)
#         diameter = Smv.query_reachable(name)
#     return diameter


def set_context(name, smv_file_content, smv_ord=""):
    global protocol_name
    protocol_name = name
    _res = Smv.compute_reachable(name, smv_file_content, smv_ord)

    # def wait_for_diameter():
    #     nonlocal diameter
    #     while True:
    #         diameter = Smv.query_reachable(name)
    #         if diameter is not None and diameter != 0:
    #             break

    # @ mak
    def wait_for_diameter():
        nonlocal diameter
        while True:
            try:
                diameter = Smv.query_reachable(name)
                if diameter is not None and diameter != 0:
                    break
            except OSError as e: 
                print("Error connecting to graylog: {}. ".format(e))
                time.sleep(30)

    diameter = None
    diameter_thread = threading.Thread(target=wait_for_diameter)
    diameter_thread.start()
    diameter_thread.join()  # 等待直径计算完成

    # print("diameter:", diameter)

    return diameter



def is_inv(inv=None, quiet=True):
    if inv in table:
        return table[inv]
    else:
        if protocol_name == "":
            raise Exception("Protocol name not set")
        else:
            r = Smv.check_inv(protocol_name, inv)
            table[inv] = r
            return r


def calculate_protocol_reachability(name, smv_file_content, smv_ord=""):
    diameter = set_context(name, smv_file_content, smv_ord)
    print(f"Protocol {name} has a reachability diameter of {diameter}")

# def check_invariants(name, invariants_list):
#     for inv in invariants_list:
#         is_true = is_inv(inv)
#         print(f"Invariant '{inv}' is {'true' if is_true else 'false'} for protocol {name}")

def check_invariants(name, invariant):
    is_true = is_inv(invariant)
    # print(f"Invariant '{invariant}' is {'true' if is_true else 'false'} for protocol {name}")
    return is_true


if __name__ == "__main__":

    # parse_name = "protocols/mutualEx/mutualEx"
    # parse_name = "protocols/mutdata/mutdata"
    # parse_name = "protocols/german_withoutData/german_withoutData"
    # parse_name = "protocols/philosopher/philosopher_smv"
    # parse_name = "protocols/german/german"
    # parse_name = "../NuSMV2/German"
    parse_name = "protocols/flash_withoutData/flash_nodata_cub"
    protocol_name = parse_name.split("/")[-1]

    # smv_content = str(parse_file(parse_name+".m", smvSelect=True))
    # with open(parse_name + ".smv", "w") as f:
    #     f.write(str(smv_content))
    smv_content = ''
    with open(parse_name + "_node2.smv", "r") as file:
        smv_content = file.read()

    calculate_protocol_reachability(protocol_name, smv_content)

    # invariant_list = "!(ShrSet[1] = FALSE & Cache[1].State = e)"
    # invariant_list = "!(Chan3[1].Cmd = empty & ExGntd = TRUE & Chan2[1].Cmd = empty & Cache[1].State = i)"
    # invariant_list = "!(Chan3[1].Cmd = empty & Chan2[1].Cmd = empty & Cache[1].State = i & Chan3[2].Cmd = empty & ExGntd = TRUE & Chan2[2].Cmd = empty & Cache[2].State = i)"
    # invariant_list = "!(ExGntd = TRUE & ShrSet[1] = FALSE)"
    # invariant_list = "!(state[1] = eating & state[2] = eating)"
    # invariant_list = "!(Sta.NakcMsg.Cmd = nakc_none & Sta.HomeProc.ProcCmd = node_none)"
    # invariant_list = "!(InvSet[2] = FALSE & Chan2[2].Cmd = empty & CurCmd = reqs & Cache[2].State = e)"

    invariant_list = "!(Sta.Dir.HeadVld = FALSE & Sta.Dir.Pending = FALSE & Sta.Dir.InvSet[1] = TRUE)"

    # invariant_list = "!(n[1] = c & n[2] = c)"
    print("check inv: ", invariant_list)
    # print("check in ......")
    print("check result: ", check_invariants(protocol_name, invariant_list))

    # file_path = "protocols/trans/flash_inv_node1"
    # with open(file_path + '.txt', "r") as file:
    #     lines = file.readlines()
    #     for line in lines:
    #         line = line.replace(";", "").replace("\n", "")
    #         match = line.split("!")[1]
    #         # print("match: ", match)
    #         inner_formula = re.sub(r'= (\w+)', lambda x: '= ' + x.group(1).lower(), str(match))
    #         invariant_list = "!" + inner_formula.replace("true", "TRUE").replace("false", "FALSE")
    #         print("check inv: ", invariant_list)
    #         print("check result: ", check_invariants(protocol_name, invariant_list))


