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
    "capstone==5.0.0rc2",
    "pyelftools",
    "unicorn==1.0.2",
]

setup(
    name="muicore",
    version="0.0.1",
    packages=find_packages(exclude=["tests", "tests.*"]),
    install_requires=[
        # manticore from upstream chess branch with fixes not yet in master
        "manticore @ git+https://github.com/trailofbits/manticore.git@634b6a4cdc295c93027b1dbe5037e574cf76200b",
        "protobuf==3.20.1",
        "grpcio==1.46.3",
        "crytic-compile==0.2.2",
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
