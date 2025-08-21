#!/usr/bin/env python3
"""Generate protobuf + grpc code from protobuf specification file."""

if __name__ == "__main__":
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