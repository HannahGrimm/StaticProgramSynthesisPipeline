import os
import sys
# ensure local package import works
sys.path.insert(0, os.path.dirname(__file__))
from translateToJava import translate_synthesized_code_to_java

synth_path = os.path.join(os.path.dirname(__file__), 'temp', 'synthesizedCode.txt')
vars = [('x', True, 'int'), ('c', True, 'int')]
print('Using synthesized file:', synth_path)
try:
    out = translate_synthesized_code_to_java(synthesized_code_path=synth_path, variable_modifiability_dict=vars)
    print('Translation output:\n', out)
except Exception as e:
    import traceback
    print('Error during translation: ', e)
    traceback.print_exc()
