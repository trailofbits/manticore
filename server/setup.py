from setuptools import Command, find_packages, setup


class GenerateCommand(Command):
    description = (
        "generates muicore server protobuf + grpc code from protobuf specification file"
    )
    user_options = []

    def initialize_options(self):
        pass

    def finalize_options(self):
        pass

    def run(self):
        from grpc.tools import protoc

        protoc.main(
            [
                "grpc_tools.protoc",
                "-I.",
                "--python_out=.",
                "--grpc_python_out=.",
                "--mypy_out=.",
                "./muicore/MUICore.proto",
            ]
        )


native_deps = [
    "capstone @ git+https://github.com/aquynh/capstone.git@1766485c0c32419e9a17d6ad31f9e218ef4f018f#subdirectory=bindings/python",
    "pyelftools",
    "unicorn==1.0.2",
]

setup(
    name="muicore",
    version="0.0.1",
    packages=find_packages(exclude=["tests", "tests.*"]),
    install_requires=[
        "manticore @ git+https://github.com/trailofbits/manticore.git@chess",
        "grpcio",
        "crytic-compile==0.2.1",
    ]
    + native_deps,
    extras_require={"dev": ["grpcio-tools"]},
    entry_points={
        "console_scripts": [
            "muicore=muicore.mui_server:main",
        ],
        "distutils.commands": ["generate = GenerateCommand"],
    },
    cmdclass={
        "generate": GenerateCommand,
    },
)
