import re

datatype_mapping_dict = {"int": "Int", "boolean": "Bool", "int[]": "(Array Int Int)"}



def replace_varname(replace_in, replace_what, replace_with):
    pattern = r"\b" + re.escape(replace_what) + r"\b"
    result = re.sub(pattern, replace_with, replace_in)
    return result


def generate_sygus_problem_old(variables, preconditions, postconditions, grammar=None):
    output = "(set-logic ALL)\n"
    output += "(declare-datatype Tuple ((empty) (mkTuple "

    # creating the tuple
    for index, var in enumerate(variables):
        output += f"(getField{str(index)} {datatype_mapping_dict[var[2]]})"
    output += ")))\n\n"

    # variables for conditions
    for var in variables:
        output += f"(declare-var {var[0]}_preCon {datatype_mapping_dict[var[2]]})\n"
        output += f"(declare-var {var[0]}_postCon {datatype_mapping_dict[var[2]]})\n"
    output += "\n"

    # Precondition and postcondition definitions
    edited_precondition = " ".join(preconditions)
    edited_postcondition = " ".join(postconditions)
    for var in variables:
        edited_precondition = replace_varname(
            edited_precondition, var[0], var[0] + "_preCon"
        )  # edited_precondition.replace(var[0], var[0] + "_preCon")
        edited_postcondition = replace_varname(
            edited_postcondition, var[0], var[0] + "_postCon"
        )  # edited_postcondition.replace(var[0], var[0] + "_postCon")

    output += "(define-fun preCondition ("
    output += " ".join(
        [f"({var[0]}_preCon {datatype_mapping_dict[var[2]]})" for var in variables]
    )
    output += ") Bool "
    output += f"(and {edited_precondition}))\n\n"  # TODO: Change variable names inside preconditions

    output += "(define-fun postCondition ("
    output += " ".join(
        [f"({var[0]}_postCon {datatype_mapping_dict[var[2]]})" for var in variables]
    )
    output += ") Bool "
    output += f"(and {edited_postcondition}))\n\n"  # TODO: Change variable names inside postconditions

    # Synth-fun targetFunction definition
    output += "(synth-fun targetFunction ("
    output += " ".join(
        [f"({var[0]} {datatype_mapping_dict[var[2]]})" for var in variables]
    )
    output += ") Tuple)\n\n"

    # variables for constraints
    for var in variables:
        output += f"(declare-var {var[0]}_in {datatype_mapping_dict[var[2]]})\n"
        output += f"(declare-var {var[0]}_out {datatype_mapping_dict[var[2]]})\n"
    output += "\n"

    # Constraint definition
    output += "(constraint (forall ("
    output += " ".join(
        [
            f"({var[0]}_in {datatype_mapping_dict[var[2]]}) ({var[0]}_out {datatype_mapping_dict[var[2]]})"
            for var in variables
        ]
    )

    output += ") "
    output += "(=>\n\t(and\n\t\t(preCondition "
    output += " ".join([f"{var[0]}_in" for var in variables])
    output += ")"

    target_func_call = (
        "(targetFunction " + " ".join([f"{var[0]}_in" for var in variables]) + ")"
    )

    for index, var in enumerate(variables):
        output += f"\n\t\t(= {var[0]}_out (getField{index} {target_func_call}))"

    output += "\n\t)\n\t(and\n\t\t(postCondition "
    output += " ".join([f"{var[0]}_out" for var in variables])
    output += ")"

    for var in variables:
        if not var[1]:
            output += f"\n\t\t(= {var[0]}_in {var[0]}_out)"

    output += "\n\t)\n)))\n(check-synth)"

    return output


def generate_sygus_problem(
    variables, preconditions, postconditions, loopVariantVar=None, grammar=None
):
    mod_vars = [(_n, _mod, _t) for (_n, _mod, _t) in variables if _mod]
    con_vars = [(_n, _mod, _t) for (_n, _mod, _t) in variables if not _mod]

    output = "(set-logic ALL)\n"
    output += "(declare-datatype Tuple ((empty) (mkTuple "

    # creating the tuple
    for index, var in enumerate(mod_vars):
        output += f"(getField{str(index)} {datatype_mapping_dict[var[2]]})"
    output += ")))\n\n"

    # variables for conditions
    for var in variables:
        output += f"(declare-var {var[0]}_preCon {datatype_mapping_dict[var[2]]})\n"
        output += f"(declare-var {var[0]}_postCon {datatype_mapping_dict[var[2]]})\n"
    if loopVariantVar:
        output += f"(declare-var {loopVariantVar} Int)\n"
    output += "\n"

    # Precondition and postcondition definitions
    edited_precondition = " ".join(preconditions)
    edited_postcondition = " ".join(postconditions)
    for var in variables:
        edited_precondition = replace_varname(
            edited_precondition, var[0], var[0] + "_preCon"
        )  # edited_precondition.replace(var[0], var[0] + "_preCon")
        edited_postcondition = replace_varname(
            edited_postcondition, var[0], var[0] + "_postCon"
        )  # edited_postcondition.replace(var[0], var[0] + "_postCon")

    output += "(define-fun preCondition ("
    output += " ".join(
        [f"({var[0]}_preCon {datatype_mapping_dict[var[2]]})" for var in variables]
    )
    if loopVariantVar:
        output += f" ({loopVariantVar} Int)"
    output += ") Bool "
    output += f"(and {edited_precondition}))\n\n"

    output += "(define-fun postCondition ("
    output += " ".join(
        [f"({var[0]}_postCon {datatype_mapping_dict[var[2]]})" for var in variables]
    )
    if loopVariantVar:
        output += f" ({loopVariantVar} Int)"
    output += ") Bool "
    output += f"(and {edited_postcondition}))\n\n"

    # Synth-fun targetFunction definition
    output += "(synth-fun targetFunction ("
    output += " ".join(
        [f"({var[0]} {datatype_mapping_dict[var[2]]})" for var in variables]
    )
    output += ") Tuple)\n\n"

    # variables for constraints
    for var in variables:
        output += f"(declare-var {var[0]}_in {datatype_mapping_dict[var[2]]})\n"
    for var in mod_vars:
        output += f"(declare-var {var[0]}_out {datatype_mapping_dict[var[2]]})\n"
    output += "\n"

    # Constraint definition
    output += "(constraint (forall ("
    for i, var in enumerate(variables):
        if i > 0:
            output += " "
        output += f"({var[0]}_in {datatype_mapping_dict[var[2]]})"
    for var in mod_vars:
        output += f" ({var[0]}_out {datatype_mapping_dict[var[2]]})"

    if loopVariantVar:
        output += f" ({loopVariantVar} Int)"

    # output += " ".join(
    #    [
    #        f"({var[0]}_in {datatype_mapping_dict[var[2]]}) ({var[0]}_out {datatype_mapping_dict[var[2]]})"
    #        for var in variables
    #    ]
    # )

    output += ") "
    output += "(=>\n\t(and\n\t\t(preCondition "
    output += " ".join([f"{var[0]}_in" for var in variables])
    if loopVariantVar:
        output += f" {loopVariantVar}"
    output += ")"

    target_func_call = (
        "(targetFunction " + " ".join([f"{var[0]}_in" for var in variables]) + ")"
    )

    for index, var in enumerate(mod_vars):
        output += f"\n\t\t(= {var[0]}_out (getField{index} {target_func_call}))"

    output += "\n\t)\n\t(and\n\t\t(postCondition"
    for _n, _m, _ in variables:
        if _m:
            output += f" {_n}_out"
        else:
            output += f" {_n}_in"
    # output += " ".join([f"{_n}{"_out" if _m else "_in"}" for (_n, _m, _) in variables])
    if loopVariantVar:
        output += f" {loopVariantVar}"
    output += ")"

    # for var in variables:
    #    if not var[1]:
    #        output += f"\n\t\t(= {var[0]}_in {var[0]}_out)"

    output += "\n\t)\n)))\n(check-synth)"

    return output
def generate_sygus_problem_with_array_update(
    variables, preconditions, postconditions, loopVariantVar=None
):
    # map host types -> SyGuS sorts
    datatype_mapping_dict = {
        "int": "Int",
        "boolean": "Bool",
        "int[]": "(Array Int Int)",
    }

    def replace_word(s, old, new):
        import re
        return re.sub(r"\b" + re.escape(old) + r"\b", new, s)

    # vars that are modified vs. not
    mod_vars = [(_n, _mod, _t) for (_n, _mod, _t) in variables if _mod]
    con_vars = [(_n, _mod, _t) for (_n, _mod, _t) in variables if not _mod]

    # array vars + their length symbols
    array_vars = [v[0] for v in variables if v[2] == "int[]"]
    arr_len = {a: f"{a}_len" for a in array_vars}

    out = []
    out.append("(set-logic ALL)")
    out.append(
        "(declare-datatype Tuple ((empty) (mkTuple "
        "(getField0 (Array Int Int)) (getField1 Int) (getField2 Int) (getField3 Int))))"
    )
    out.append("")

    # declare pre/post copies of variables
    for n, _, t in variables:
        out.append(f"(declare-var {n}_preCon {datatype_mapping_dict[t]})")
        out.append(f"(declare-var {n}_postCon {datatype_mapping_dict[t]})")
    # declare pre/post copies of array lengths
    for a in array_vars:
        out.append(f"(declare-var {arr_len[a]}_preCon Int)")
        out.append(f"(declare-var {arr_len[a]}_postCon Int)")
    if loopVariantVar:
        out.append(f"(declare-var {loopVariantVar} Int)")
    out.append("")

    # join user pre/post then rewrite seq.* -> arrays + _len placeholders
    pre_str = " ".join(preconditions).strip()
    post_str = " ".join(postconditions).strip()

    # 1) seq.nth A i -> select A i   2) (seq.len A) -> A_len
    for a in array_vars:
        import re
        pre_str = re.sub(r"\(seq\.nth\s+" + re.escape(a) + r"\s+",
                         f"(select {a} ", pre_str)
        post_str = re.sub(r"\(seq\.nth\s+" + re.escape(a) + r"\s+",
                          f"(select {a} ", post_str)
        pre_str = re.sub(r"\(seq\.len\s+" + re.escape(a) + r"\s*\)",
                         arr_len[a], pre_str)
        post_str = re.sub(r"\(seq\.len\s+" + re.escape(a) + r"\s*\)",
                          arr_len[a], post_str)

    # 3) suffix _preCon/_postCon on names (both base vars and *_len)
    for n, _, _t in variables:
        pre_str = replace_word(pre_str, n, f"{n}_preCon")
        post_str = replace_word(post_str, n, f"{n}_postCon")
    for a in array_vars:
        pre_str = replace_word(pre_str, arr_len[a], f"{arr_len[a]}_preCon")
        post_str = replace_word(post_str, arr_len[a], f"{arr_len[a]}_postCon")

    # preCondition signature: vars + each A_len
    sig_pre = []
    for n, _, t in variables:
        sig_pre.append(f"({n}_preCon {datatype_mapping_dict[t]})")
        if t == "int[]":
            sig_pre.append(f"({arr_len[n]}_preCon Int)")
    if loopVariantVar:
        sig_pre.append(f"({loopVariantVar} Int)")
    out.append(f"(define-fun preCondition ({' '.join(sig_pre)}) Bool "
               f"{'(and ' + pre_str + ')' if pre_str else 'true'})")
    out.append("")

    # postCondition signature: vars + each A_len
    sig_post = []
    for n, _, t in variables:
        sig_post.append(f"({n}_postCon {datatype_mapping_dict[t]})")
        if t == "int[]":
            sig_post.append(f"({arr_len[n]}_postCon Int)")
    if loopVariantVar:
        sig_post.append(f"({loopVariantVar} Int)")
    out.append(f"(define-fun postCondition ({' '.join(sig_post)}) Bool (and {post_str}))")
    out.append("")

    # synth target: inputs = vars + each A_len
    sig_fun = []
    for n, _, t in variables:
        sig_fun.append(f"({n} {datatype_mapping_dict[t]})")
        if t == "int[]":
            sig_fun.append(f"({arr_len[n]} Int)")
    out.append(f"(synth-fun targetFunction ({' '.join(sig_fun)}) Tuple )")
    out.append("")

    # universals ( _in / _out ), plus *_len_in for arrays
    for n, _, t in variables:
        out.append(f"(declare-var {n}_in {datatype_mapping_dict[t]})")
        if t == "int[]":
            out.append(f"(declare-var {arr_len[n]}_in Int)")
    for n, m, t in mod_vars:
        out.append(f"(declare-var {n}_out {datatype_mapping_dict[t]})")
    out.append("")

    # forall header
    forall_parts = []
    for n, _, t in variables:
        forall_parts.append(f"({n}_in {datatype_mapping_dict[t]})")
        if t == "int[]":
            forall_parts.append(f"({arr_len[n]}_in Int)")
    for n, m, t in mod_vars:
        forall_parts.append(f"({n}_out {datatype_mapping_dict[t]})")
    if loopVariantVar:
        forall_parts.append(f"({loopVariantVar} Int)")

    out.append(f"(constraint (forall ({' '.join(forall_parts)}) (=>")
    out.append("\t(and")

    # call preCondition with *_preCon -> *_in mapping
    call_pre = []
    for n, _, t in variables:
        call_pre.append(f"{n}_in")
        if t == "int[]":
            call_pre.append(f"{arr_len[n]}_in")
    if loopVariantVar:
        call_pre.append(loopVariantVar)
    out.append(f"\t\t(preCondition {' '.join(call_pre)})")

    # targetFunction call args
    tf_args = []
    for n, _, t in variables:
        tf_args.append(f"{n}_in")
        if t == "int[]":
            tf_args.append(f"{arr_len[n]}_in")
    tf_call = f"(targetFunction {' '.join(tf_args)})"

    # unpack tuple for each modified var in order (getField0..)
    for idx, (n, _, _) in enumerate(mod_vars):
        out.append(f"\t\t(= {n}_out (getField{idx} {tf_call}))")

    out.append("\t)")
    out.append("\t(and")
    # call postCondition with *_postCon -> *_out (or *_in for consts)
    call_post = []
    for n, m, t in variables:
        call_post.append(f"{n}_{'out' if m else 'in'}")
        if t == "int[]":
            call_post.append(f"{arr_len[n]}_in")  # length is unchanged, so use _in
    if loopVariantVar:
        call_post.append(loopVariantVar)
    out.append(f"\t\t(postCondition {' '.join(call_post)})")
    out.append("\t)\n)))")
    out.append("(check-synth)")

    return "\n".join(out)



if __name__ == "__main__":
    # Example input
    variables = [("t", True, "int"), ("c", False, "int"), ("d", False, "int")]
    preconditions = ["(= t (int.add c d))"]
    postconditions = ["(= t (int.add c 1))"]

    output_string = generate_sygus_problem(variables, preconditions, postconditions)
    print(output_string)
