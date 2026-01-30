from sygus_utils import generate_sygus_problem_with_array_update
variables = [("A", True, "int[]"), ("i", False, "int"), ("x", False, "int")]
preconditions = []
postconditions = ["(= (select A_postCon i_postCon) x_postCon)"]
print(generate_sygus_problem_with_array_update(variables, preconditions, postconditions))