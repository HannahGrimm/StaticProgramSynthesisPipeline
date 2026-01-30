import subprocess
import os

def run_cvc5(input_file, output_file, timeout=30):
    cvc5_path = "C:\\Users\\hanna\\OneDrive\\Dokumente\\Masterarbeit\\ProgSynthProgram\\ProgramSynthesisPipeline\\Code\\pythonScripts\\cvc5.exe"

    def try_run(args, desc):
        try:
            with open(output_file, "w") as out_file:
                subprocess.run(
                    args,
                    stdout=out_file,
                    stderr=subprocess.DEVNULL,
                    timeout=timeout,
                    check=True
                )
            print(f"✅ {desc} succeeded.")
            return 0
        except subprocess.TimeoutExpired:
            print(f"⏳ Timeout: {desc} took too long.")
            return -1
        except FileNotFoundError:
            print("❌ Error: cvc5.exe not found.")
            return -1
        except subprocess.CalledProcessError as e:
            print(f"❌ Error: {desc} failed.")
            return e.returncode

    print("Start Sygus")
    result = try_run(
        [cvc5_path, "--lang=sygus2", "--full-sygus-verify", input_file],
        "cvc5 with full verify"
    )

    if result != 0:
        print("🔁 Retrying without full verify ...")
        result = try_run(
            [cvc5_path, "--lang=sygus2", input_file],
            "cvc5 without full verify"
        )

    print("End Sygus")
    return result
