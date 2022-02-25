import setuptools


native_deps = [
    "capstone @ git+https://github.com/aquynh/capstone.git@1766485c0c32419e9a17d6ad31f9e218ef4f018f#subdirectory=bindings/python",
    "pyelftools",
    "unicorn==1.0.2",
]

setuptools.setup(
    name="muicore",
    version="0.0.1",
    py_modules=[
        "mui_server",
        "MUICore_pb2_grpc",
        "MUICore_pb2",
        "introspect_plugin",
        "utils",
    ],
    install_requires=[
        "manticore @ git+https://github.com/trailofbits/manticore.git@chess",
        "grpcio",
    ]
    + native_deps,
    entry_points={
        "console_scripts": [
            "muicore=mui_server:main",
        ]
    },
)
