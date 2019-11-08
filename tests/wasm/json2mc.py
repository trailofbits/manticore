import argparse
import json
from jinja2 import Environment, FileSystemLoader
from base64 import b64encode
from copy import copy

parser = argparse.ArgumentParser("Generate Manticore tests from the WASM Spec")
parser.add_argument("filename", type=argparse.FileType("r"), help="JSON file output from wast2json")
args = parser.parse_args()

data = json.load(args.filename)["commands"]
args.filename.close()


class Module:
    def __init__(self, filename, tests, name=None):
        self.name = filename.replace(".wasm", "").replace(".wast", "").replace(".", "_").strip()
        self.filename = filename
        self.tests = tests
        self.registered_name = name
        self.imports = []

    def add_test(self, name, line, args, rets, type_="assert_return", mod_name=None):
        self.tests.append(
            {
                "func": name,
                "line": line,
                "args": args,
                "rets": rets,
                "type": type_,
                "mod_name": mod_name,
            }
        )

    def __repr__(self):
        return f"<Module {self.filename} containing {len(self.tests)} tests>"


def convert_types(to_convert):
    """ Convert unsigned ints from JSON into WASM Types (I32, F64, etc) """
    out = []
    for item in to_convert:
        out.append(f"{item['type'].upper()}({item.get('value', 0)})")
    return ", ".join(out)


env = Environment(loader=FileSystemLoader("."))


def escape_null(in_str: str):
    """Base64-encode function names if they contain nonprintable characters"""
    if in_str.isprintable() and not any((c in in_str) for c in {'"', "'", ";"}):
        return f'"{in_str}"'
    else:
        return f"str(b64decode(\"{b64encode(in_str.encode('utf-8')).decode('utf-8')}\"), 'utf-8')"


env.filters["escape_null"] = escape_null

template = env.get_template("test_template.jinja2")


modules = []
registered_modules = {}
imports = []
current_module = None
for d in data:

    if d["type"] == "action":
        if d["action"]["type"] == "invoke":
            if isinstance(current_module, int):
                modules[current_module].add_test(
                    d["action"]["field"],
                    d["line"],
                    convert_types(d["action"]["args"]),
                    convert_types(d["expected"]),
                    "action",
                    mod_name=d["action"].get("module", None),
                )
        else:
            raise NotImplementedError("action with action type: " + d["action"]["type"])
    elif d["type"] == "assert_exhaustion":
        pass
    elif d["type"] == "assert_invalid":
        if current_module:
            modules[current_module].imports = copy(imports)
        current_module = None
    elif d["type"] == "assert_malformed":
        if current_module:
            modules[current_module].imports = copy(imports)
        current_module = None
    elif d["type"] == "assert_return":
        if d["action"]["type"] == "invoke":
            if isinstance(current_module, int):
                modules[current_module].add_test(
                    d["action"]["field"],
                    d["line"],
                    convert_types(d["action"]["args"]),
                    convert_types(d["expected"]),
                    mod_name=d["action"].get("module", None),
                )
        elif d["action"]["type"] == "get":
            modules[current_module].add_test(
                d["action"]["field"],
                d["line"],
                [],
                convert_types(d["expected"]),
                "assert_global",
                d["action"].get("module", None),
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
                    convert_types(d["action"]["args"]),
                    convert_types(d["expected"]),
                    "assert_trap",
                    mod_name=d["action"].get("module", None),
                )
        else:
            raise NotImplementedError("assert_trap with action type: " + d["action"]["type"])
    elif d["type"] == "assert_uninstantiable":
        if current_module:
            modules[current_module].imports = copy(imports)
        current_module = None
    elif d["type"] == "assert_unlinkable":
        if current_module:
            modules[current_module].imports = copy(imports)
        current_module = None
    elif d["type"] == "module":
        modules.append(Module(d["filename"], [], d.get("name", None)))
        if current_module:
            modules[current_module].imports = copy(imports)
        if d.get("name", None):
            imports.append({"type": "import", "name": d["name"], "filename": d["filename"]})
        current_module = len(modules) - 1
        if "name" in d:
            registered_modules[d["name"]] = modules[current_module].filename
    elif d["type"] == "register":  # Allow a module to go by another name
        maybe_name = d.get("name", False)
        if maybe_name:  # This is an alias for another registered module
            imports.append({"type": "alias", "alias": d["as"], "orig": maybe_name})
        else:  # This is an alias for the current module
            imports.append(
                {"type": "import", "name": d["as"], "filename": modules[current_module].filename}
            )
            modules[current_module].registered_name = d["as"]

    if current_module:
        modules[current_module].imports = copy(imports)

print(template.render(modules=modules))
