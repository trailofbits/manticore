from pathlib import Path

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


setup(
    name="muicore",
    version="0.0.1",
    packages=find_packages(exclude=["tests", "tests.*"]),
    python_requires=">=3.7",
    install_requires=[
        f"manticore[native] @ file://{Path(__file__).parent.resolve()}/..",
        "protobuf~=3.20",
        "grpcio~=1.46",
        "crytic-compile>=0.2.2",
    ],
    extras_require={
        "dev": [
            "grpcio-tools",
            "mypy-protobuf",
            "shiv~=1.0.1",
            "types-setuptools",
            "mypy-protobuf",
            "black~=22.0",
            "isort==5.10.1",
            "mypy==0.942",
        ]
    },
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
