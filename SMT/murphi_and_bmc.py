import sys
import time
import subprocess
import BMC
import threading

def run_shell_command(command):
    try:
        # 执行Shell命令
        result = subprocess.run(command, shell=True, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)

        target_string = "No error found"

        result_std = result.stdout.decode('utf-8')

        # print("result: ", result.stderr)
        if target_string in result_std:
            return True
        elif "failed" in result_std:
            return False
        else:
            # 返回命令的输出结果
            # print("The %s was successfully executed\n" % command)
            # return result.strip()
            return ''

    except subprocess.CalledProcessError as e:
        # 如果命令执行失败，打印错误信息并返回空字符串或其他错误处理方式
        print(f"%s execution failed: {e}" % command)
        return ""

def shell_cmd(file_name):
    # update mu.o in src
    # res += run_shell_command("cd ../../cmurphi_LS/test/mutual_nodata/")

    res = run_shell_command(f"../../cmurphi_LS/src/mu ../../cmurphi_LS/test/{file_name}.m")
    res = run_shell_command(f"g++ -ggdb -o ../../cmurphi_LS/test/{file_name}.o ../../cmurphi_LS/test/{file_name}.cpp -I ../../cmurphi_LS/include -lm")
    res = run_shell_command(f"../../cmurphi_LS/test/{file_name}.o -localsearch -m5000 -p5")
    return res

def exec_murphi(inv_p, f_name, file_num):
    sys.stdout = open("./FileLog/flash3_murphi_check.log", 'w')
    sys.stderr = open("./FileLog/flash3_murphi_check.log", 'w')
    s_murphi = time.time()
    for k in range(1, file_num+1):
        # inv_path = f"{inv_p}{k}"
        # file_name = f"{f_name}{k}"

        inv_path = f"{inv_p}{k}"
        file_name = f"{f_name}{k}"
        protocol_name = file_name.split("/")[-1]

        with open(inv_path + ".m", 'r') as file:
            lines = file.readlines()
        for line in lines:
            if "!(" in line:
                inv_str = line
    
        inv = inv_str.strip()

        print(f"The Inv in {protocol_name} is: ", inv)

        output = shell_cmd(file_name)
        print("The result of checking Inv in murphi: ", output)
        print("\n")
    e_murphi = time.time()
    murphi_time = e_murphi - s_murphi
    print(f"murphi runtime: {murphi_time:.6f} s")
    sys.stdout.close()
    sys.stderr.close()

def exec_BMC(inv_p, mf_p, f_name, node_num, file_num):
    sys.stdout = open("./FileLog/flash3_BMC_check.log", 'w')
    sys.stderr = open("./FileLog/flash3_BMC_check.log", 'w')
    s_BMC = time.time()
    for k in range(1, file_num+1):
        # inv_path = f"../protocols/mutual_nodata_benchmark/mutualEx_{k}"
        # mfile_path = "../protocols/mutualEx/mutualEx"
        # file_name = f"mutual_nodata/mutualEx_{k}"

        inv_path = f"{inv_p}{k}"
        mfile_path = mf_p
        file_name = f"{f_name}{k}"
        protocol_name = file_name.split("/")[-1]

        with open(inv_path + ".m", 'r') as file:
            lines = file.readlines()
        for line in lines:
            if "!(" in line:
                inv_str = line
    
        inv = inv_str.strip()
        node_number = node_num
        node_permutations = list()
        node_list = list()
        for i in range(1, node_number + 1):
            node_permutations.append(i)
            node_list.append(chr(ord('i') + int(i) - 1))

        upper_bound = 10

        inv_check_result, inv = BMC.call_BMC(upper_bound, inv, mfile_path, node_permutations = node_permutations, node_list = node_list)

        print(f"The Inv in {protocol_name} is: ", inv)
        print("The result of checking Inv in BMC: ", inv_check_result)
        print("\n")
    e_BMC = time.time()
    BMC_time = e_BMC - s_BMC
    print(f"BMC runtime: {BMC_time:.6f} s")
    sys.stdout.close()
    sys.stderr.close()

def execute_in_thread(inv_p, mf_p, f_name, node_num, file_num):
    thread1 = threading.Thread(target=exec_murphi, args=(inv_p, f_name, file_num), name="Murphi_thread")
    thread2 = threading.Thread(target=exec_BMC, args=(inv_p, mf_p, f_name, node_num, file_num), name="BMC_thread")
    thread1.start()
    thread2.start()
    thread1.join()
    thread2.join()


if __name__ == "__main__":
    # file_path = "../../cmurphi_LS/test/mutual_nodata/"
    # 调用
    # sys.stdout = open("./FileLog/mutualEx_Inv_check.log", 'w')
    # sys.stderr = open("./FileLog/mutualEx_Inv_check.log", 'w')
    # sys.stdout = open("./FileLog/germanwithdata_Inv_check.log", 'w')
    # sys.stderr = open("./FileLog/germanwithdata_Inv_check.log", 'w')
    # sys.stdout = open("./FileLog/german2_BMC_check.log", 'w')
    # sys.stderr = open("./FileLog/german2_BMC_check.log", 'w')
    sys.stdout = open("./FileLog/flash2_BMCNG_check.log", 'w')
    sys.stderr = open("./FileLog/flash2_BMCNG_check.log", 'w')
    # sys.stdout = open("./FileLog/decen_Inv_check_debug.log", 'w')
    # sys.stderr = open("./FileLog/decen_Inv_check_debug.log", 'w')
    start_time = time.time()

    upper_bound = 15
    lower_procount = 0
    upper_procount = 10
    # mfile_path = "../protocols/german_withdata/german"
    mfile_path = "../protocols/flash_withData/flash_data_cub"

    s_formula_time = time.time()
    init_formula, axiom_formula, all_LTL_formula, ScalarSetType_vars, BooleanType_vars, negGuard_formula = BMC.get_BMC_formula(lower_procount, upper_procount, upper_bound, mfile_path)
    all_init_formula = list()
    for neguard in negGuard_formula:
        neg_guard = neguard
        
        guard_result, new_init_formula = BMC.call_BMC_guard(init_formula, axiom_formula, all_LTL_formula, upper_bound, neg_guard, mfile_path, ScalarSetType_vars, BooleanType_vars)
        # inv_check_result, inv = call_BMC(new_init_formula, axiom_formula, all_LTL_formula, upper_bound, check_inv, mfile_path, ScalarSetType_vars, BooleanType_vars)
        
        all_init_formula.append(new_init_formula)
    e_formula_time = time.time()
    a_formula_time = e_formula_time - s_formula_time
    print(f"the time of bmc formula is {a_formula_time:.6f} s")

    for k in range(1, 70):
        # inv_path = f"../protocols/mutual_nodata_benchmark/mutualEx_{k}"
        # mfile_path = "../protocols/mutualEx/mutualEx"
        # file_name = f"mutual_nodata/mutualEx_{k}"

        # inv_path = f"../protocols/german_data_benchmark/german_{k}"
        # file_name = f"german_withdata/german_{k}"
        inv_path = f"../protocols/flash_data_2/flash_{k}"
        # file_name = f"german_withdata/german_{k}"
        # inv_path = f"../protocols/decentralized_lock_inv/decen_{k}"
        # mfile_path = "../protocols/decentralized_lock/decentralized_lock"
        # file_name = f"decentralized_lock/decen_{k}"
        protocol_name = mfile_path.split("/")[-1]

        with open(inv_path + ".m", 'r') as file:
            lines = file.readlines()
        for i in range(len(lines)):
            line = lines[i]
            if "invariant" in line:
                next_line_idx = i + 1
                if next_line_idx < len(lines):
                    inv_str = lines[next_line_idx]
        check_inv = inv_str.strip()

        # bmc_check_inv, negInv_formula = get_Inv_formula(upper_bound, inv, mfile_path, node_number)

        # inv_check_result, inv = BMC.call_BMC(init_fomula, axiom_formula, all_LTL_formula, upper_bound, inv, mfile_path, node_number)

        # inv_check_result, inv = BMC.call_BMC(upper_bound, inv, mfile_path, node_number)

        s_bmc_time = time.time()
        # inv_check_result, inv = BMC.call_BMC(init_formula, axiom_formula, all_LTL_formula, upper_bound, check_inv, mfile_path, ScalarSetType_vars, BooleanType_vars)
        results = BMC.mul_process_guard(check_inv, all_init_formula, axiom_formula, all_LTL_formula, ScalarSetType_vars, BooleanType_vars, upper_bound, mfile_path)
        e_bmc_time = time.time()
        a_bmc_time = e_bmc_time - s_bmc_time
        print(f"The Inv in {protocol_name}_{k} is: ", check_inv)
        print("The result of checking Inv in BMC: ", results)
        print(f"the time of bmc check is {a_bmc_time:.6f} s")
        print("\n")

        # output = shell_cmd(file_name)

        # print("The result of checking Inv in murphi: ", output)
        # if output == results:
        #     print("Consistency of results is : YES")
        # else:
        #     print("Consistency of results is : NO")
        # print("\n")

    # inv_path = "../protocols/mutual_nodata_benchmark/mutualEx_"
    # mfile_path = "../protocols/mutualEx/mutualEx"
    # file_name = "mutual_nodata/mutualEx_"

    # inv_path = "../protocols/german_4/german_"
    # mfile_path = "../protocols/german_withdata/german"
    # file_name = "german_4/german_"

    # inv_path = "../protocols/flash_3/flash_"
    # mfile_path = "../protocols/flash_withoutData/flash_nodata_cub"
    # file_name = "flash_3/flash_"
    # node_num = 3
    # file_num = 300
    # execute_in_thread(inv_path, mfile_path, file_name, node_num, file_num)
    end_time = time.time()
    shell_run_time = end_time - start_time
    
    print(f"shell runtime: {shell_run_time:.6f} s")

    sys.stdout.close()
    sys.stderr.close()

