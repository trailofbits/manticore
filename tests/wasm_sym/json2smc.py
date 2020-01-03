import argparse
import json
from jinja2 import Environment, FileSystemLoader
from base64 import b64encode
import string

parser = argparse.ArgumentParser("Generate Manticore tests from the WASM Spec")
parser.add_argument("filename", type=argparse.FileType("r"), help="JSON file output from wast2json")
args = parser.parse_args()

data = json.load(args.filename)["commands"]
args.filename.close()

# Individual unit tests that we skip due to timeouts or problematic statefulness
skip = {
    "fib_L261",
    "check-memory-zero_L87",
    "check-memory-zero_L89",
    "check-memory-zero_L91",
    "check-memory-zero_L93",
    "check-memory-zero_L95",
    "check-memory-zero_L97",
    "odd_L269",
    "fib-i64_L527",
}
# Modules with statefeulness for which we disallow reinitialization
disallow_reinit_modules = {
    "call_0",
    "call_indirect_0",
    "globals_0",
    "memory_grow_0",
    "memory_grow_3",
}


class Module:
    def __init__(self, filename, tests):
        self.name = filename.replace(".wasm", "").replace(".wast", "").replace(".", "_").strip()
        self.filename = filename
        self.tests = tests
        self.allow_reinit = True if self.name not in disallow_reinit_modules else False

    def add_test(self, name, line, args, rets, type_="assert_return"):
        self.tests.append({"func": name, "line": line, "args": args, "rets": rets, "type": type_})

    def __repr__(self):
        return f"<Module {self.filename} containing {len(self.tests)} tests>"


def convert_args(to_convert):
    """
    Convert a set of unsigned ints from JSON into an appropriate set of constraints
    :param to_convert:
    :return:
    """
    out = []
    for idx, item in enumerate(to_convert):
        if "32" in item["type"]:
            out.append(
                {"constraint": f"state.new_symbolic_value(32)", "val": int(item.get("value", 0))}
            )
        elif "64" in item["type"]:
            out.append(
                {"constraint": f"state.new_symbolic_value(64)", "val": int(item.get("value", 0))}
            )
        else:
            raise RuntimeError("garbage type")
    return out


def convert_rets(to_convert):
    """Convert unsigned int from JSON into concrete values"""
    out = []
    for item in to_convert:
        out.append(f"{item['type'].upper()}({item.get('value', 0)})")
    return ", ".join(out)


env = Environment(loader=FileSystemLoader("."))


def escape_null(in_str: str):
    """ Base-64 encode non-printable characters in test names so we can handle that obnoxious names module """
    if in_str.isprintable() and not any((c in in_str) for c in {'"', "'", ";"}):
        return f'"{in_str}"'
    else:
        return f"str(b64decode(\"{b64encode(in_str.encode('utf-8')).decode('utf-8')}\"), 'utf-8')"


env.filters["escape_null"] = escape_null

template = env.get_template("symbolic_test_template.jinja2")


modules = []
current_module = None
for d in data:
    if f"{d.get('action', {}).get('field', None)}_L{d['line']}" in skip:
        continue

    if d["type"] == "action":
        if d["action"]["type"] == "invoke":
            if isinstance(current_module, int):
                modules[current_module].add_test(
                    d["action"]["field"],
                    d["line"],
                    convert_args(d["action"]["args"]),
                    convert_rets(d["expected"]),
                    "action",
                )
        else:
            raise NotImplementedError("action with action type: " + d["action"]["type"])
    elif d["type"] == "assert_exhaustion":
        pass
    elif d["type"] == "assert_invalid":
        current_module = None
    elif d["type"] == "assert_malformed":
        current_module = None
    elif d["type"] == "assert_return":
        if d["action"]["type"] == "invoke":
            if isinstance(current_module, int):
                modules[current_module].add_test(
                    d["action"]["field"],
                    d["line"],
                    convert_args(d["action"]["args"]),
                    convert_rets(d["expected"]),
                )
        else:
            raise NotImplementedError("assert_return with action type: " + d["action"]["type"])
    elif d["type"] == "assert_return_arithmetic_nan":
        # XXX Eventually implement, but if we raise here it eliminates other valid tests
        # raise NotImplementedError("assert_return_arithmetic_nan")
        pass

    elif d["type"] == "assert_return_canonical_nan":
        # XXX Eventually implement, but if we raise here it eliminates other valid tests
        # raise NotImplementedError("assert_return_canonical_nan")
        pass

    elif d["type"] == "assert_trap":
        if d["action"]["type"] == "invoke":
            if isinstance(current_module, int):
                modules[current_module].add_test(
                    d["action"]["field"],
                    d["line"],
                    convert_args(d["action"]["args"]),
                    convert_rets(d["expected"]),
                    "assert_trap",
                )
        else:
            raise NotImplementedError("assert_trap with action type: " + d["action"]["type"])
    elif d["type"] == "assert_uninstantiable":
        current_module = None
    elif d["type"] == "assert_unlinkable":
        current_module = None
    elif d["type"] == "module":
        modules.append(Module(d["filename"], []))
        current_module = len(modules) - 1
    elif d["type"] == "register":
        raise NotImplementedError("register")

print(template.render(modules=modules))
