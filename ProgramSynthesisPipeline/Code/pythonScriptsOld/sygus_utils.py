import re
datatype_mapping_dict = {"int": "Int", "boolean": "Bool", "int[]": "(Array Int Int)"}

def generate_sygus_problem_with_array_update(
    variables, preconditions, postconditions, loopVariantVar=None
):
    datatype_mapping_dict = {
        "int": "Int",
        "boolean": "Bool",
        "int[]": "(Array Int Int)"
    }

    def replace_varname(replace_in, replace_what, replace_with):
        import re
        pattern = r"\b" + re.escape(replace_what) + r"\b"
        return re.sub(pattern, replace_with, replace_in)

    mod_vars = [(_n, _mod, _t) for (_n, _mod, _t) in variables if _mod]
    con_vars = [(_n, _mod, _t) for (_n, _mod, _t) in variables if not _mod]

    output = "(set-logic ALL)\n"
    output += "(declare-datatype Tuple ((empty) (mkTuple "
    output += "(getField0 (Array Int Int)) "
    output += "(getField1 Int) (getField2 Int) (getField3 Int)"
    output += ")))\n\n"

    for var in variables:
        output += f"(declare-var {var[0]}_preCon {datatype_mapping_dict[var[2]]})\n"
        output += f"(declare-var {var[0]}_postCon {datatype_mapping_dict[var[2]]})\n"
    if loopVariantVar:
        output += f"(declare-var {loopVariantVar} Int)\n"
    output += "\n"

    edited_precondition = " ".join(preconditions).strip()
    edited_postcondition = " ".join(postconditions).strip()

    for var in variables:
        edited_precondition = replace_varname(edited_precondition, var[0], var[0] + "_preCon")
        edited_postcondition = replace_varname(edited_postcondition, var[0], var[0] + "_postCon")

    output += "(define-fun preCondition ("
    output += " ".join(
        [f"({var[0]}_preCon {datatype_mapping_dict[var[2]]})" for var in variables]
    )
    if loopVariantVar:
        output += f" ({loopVariantVar} Int)"
    output += ") Bool "
    output += f"{'(and ' + edited_precondition + ')' if edited_precondition else 'true'})\n\n"

    output += "(define-fun postCondition ("
    output += " ".join(
        [f"({var[0]}_postCon {datatype_mapping_dict[var[2]]})" for var in variables]
    )
    if loopVariantVar:
        output += f" ({loopVariantVar} Int)"
    output += ") Bool "
    output += f"(and {edited_postcondition}))\n\n"


    output += "(synth-fun targetFunction ("
    output += " ".join([f"({var[0]} {datatype_mapping_dict[var[2]]})" for var in variables])
    output += ") Tuple"
    output += " )\n\n"

    for var in variables:
        output += f"(declare-var {var[0]}_in {datatype_mapping_dict[var[2]]})\n"
    for var in mod_vars:
        output += f"(declare-var {var[0]}_out {datatype_mapping_dict[var[2]]})\n"
    output += "\n"

    output += "(constraint (forall ("
    output += " ".join([f"({var[0]}_in {datatype_mapping_dict[var[2]]})" for var in variables])
    output += " "
    output += " ".join([f"({var[0]}_out {datatype_mapping_dict[var[2]]})" for var in mod_vars])
    if loopVariantVar:
        output += f" ({loopVariantVar} Int)"
    output += ") "
    output += "(=>\n\t(and\n\t\t(preCondition "
    output += " ".join([f"{var[0]}_in" for var in variables])
    if loopVariantVar:
        output += f" {loopVariantVar}"
    output += ")"

    target_func_call = "(targetFunction " + " ".join([f"{var[0]}_in" for var in variables]) + ")"

    for index, var in enumerate(mod_vars):
        output += f"\n\t\t(= {var[0]}_out (getField{index} {target_func_call}))"

    output += "\n\t)\n\t(and\n\t\t(postCondition"
    for (_n, _m, _) in variables:
        output += f" {_n}_{'out' if _m else 'in'}"
    if loopVariantVar:
        output += f" {loopVariantVar}"
    output += ")"
    output += "\n\t)\n)))\n(check-synth)"

    return output
