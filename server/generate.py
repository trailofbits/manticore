"""Custom setuptools command for generating protobuf code."""

from setuptools import Command


class GenerateCommand(Command):
    """Generates manticore_server protobuf + grpc code from protobuf specification file."""
    
    description = "generates manticore_server server protobuf + grpc code from protobuf specification file"
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
                "./manticore_server/ManticoreServer.proto",
            ]
        )