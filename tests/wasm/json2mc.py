import argparse
import json
from jinja2 import Environment, FileSystemLoader

parser = argparse.ArgumentParser("Generate Manticore tests from the WASM Spec")
parser.add_argument("filename", type=argparse.FileType("r"), help="JSON file output from wast2json")
args = parser.parse_args()

data = json.load(args.filename)["commands"]


class Module:
    def __init__(self, filename, tests):
        self.name = filename.replace(".wasm", "").replace(".wast", "").replace(".", "_").strip()
        self.filename = filename
        self.tests = tests

    def __repr__(self):
        return f"<Module {self.filename} containing {len(self.tests)} tests>"


def convert_types(to_convert):
    out = []
    for item in to_convert:
        out.append(f"{item['type'].upper()}({item.get('value', None)})")
    return ", ".join(out)


env = Environment(loader=FileSystemLoader("."))
template = env.get_template("test_template.jinja2")

modules = []
current_module = None
for d in data:
    if d["type"] == "action":
        raise NotImplementedError("action")
    elif d["type"] == "assert_exhaustion":
        pass
    elif d["type"] == "assert_invalid":
        current_module = None
    elif d["type"] == "assert_malformed":
        current_module = None
    elif d["type"] == "assert_return":
        if d["action"]["type"] == "invoke":
            if isinstance(current_module, int):
                modules[current_module].tests.append(
                    {
                        "func": d["action"]["field"],
                        "args": convert_types(d["action"]["args"]),
                        "rets": convert_types(d["expected"]),
                    }
                )
        else:
            raise NotImplementedError("assert_return")
    elif d["type"] == "assert_return_arithmetic_nan":
        raise NotImplementedError("assert_return_arithmetic_nan")
    elif d["type"] == "assert_return_canonical_nan":
        raise NotImplementedError("assert_return_canonical_nan")
    elif d["type"] == "assert_trap":
        if d["action"]["type"] == "invoke":
            pass
            # if isinstance(current_module, int):
            #     modules[current_module].tests.append({"func": d["action"]["field"],
            #                                           "args": convert_types(d["action"]["args"]),
            #                                           "rets": convert_types(d["expected"])})
        else:
            raise NotImplementedError("assert_trap")
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
