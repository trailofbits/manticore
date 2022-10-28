import grpc
from grpc._server import _Context


class MockContext(_Context):
    def __init__(self) -> None:
        self.code: grpc.StatusCode = grpc.StatusCode.OK
        self.details: str = ""

    def set_details(self, details: str) -> None:
        self.details = details

    def set_code(self, code: grpc.StatusCode) -> None:
        self.code = code

    def reset(self):
        self.code: grpc.StatusCode = grpc.StatusCode.OK
        self.details: str = ""
