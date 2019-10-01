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

skip = {"fib_L261", "check-memory-zero_L87", "odd_L269"}


class Module:
    def __init__(self, filename, tests):
        self.name = filename.replace(".wasm", "").replace(".wast", "").replace(".", "_").strip()
        self.filename = filename
        self.tests = tests

    def add_test(self, name, line, args, rets, type_="assert_return"):
        self.tests.append({"func": name, "line": line, "args": args, "rets": rets, "type": type_})

    def __repr__(self):
        return f"<Module {self.filename} containing {len(self.tests)} tests>"


def convert_args(to_convert):
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
    out = []
    for item in to_convert:
        out.append(f"{item['type'].upper()}({item.get('value', 0)})")
    return ", ".join(out)


env = Environment(loader=FileSystemLoader("."))


def escape_null(in_str: str):
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
