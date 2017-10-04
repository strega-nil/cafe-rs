import sys
import os
import re
from subprocess import call

def fail(name, exit_code):
    print("failure to compile '", name, "': ", exit_code, file=sys.stderr)
    sys.exit(1)
def succeed(name):
    print("accidentally compiled '", name, "' successfully", file=sys.stderr)
    sys.exit(1)

if call(["cargo", "build"]) != 0:
    sys.exit(1)

print("\nrunning succeed tests")

tests_succeed = "./language/tests-succeed/"
for file in os.listdir(path=tests_succeed):
    if re.match(".*\\.cf", file):
        print("compiling ", file)
        res = call(["cargo", "run", "-q", "--", tests_succeed + file]) 
        if res != 0:
            fail(file, res)
    else:
        print("weird file found in tests-succeed: ", file, file=sys.stderr)

tests_fail = './language/tests-fail/'
for file in os.listdir(path=tests_fail):
    if re.match(".*\\.cf", file):
        print("compiling ", file, end="\n    ")
        res = call(["cargo", "run", "-q", "--", "--no-run", tests_fail + file])
        if res == 0:
            succeed(file)
    else:
        print("weird file found in tests-fail: ", file, file=sys.stderr)