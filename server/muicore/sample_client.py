import grpc
import MUICore_pb2_grpc
import MUICore_pb2
import time

addrs = [0x401F70, 0x401F9B]


def run():
    with grpc.insecure_channel("localhost:50010") as channel:
        stub = MUICore_pb2_grpc.ManticoreUIStub(channel)
        #        av1 = stub.TargetAddress(MUICore_pb2.AddressRequest(address=addrs[0],type=MUICore_pb2.AddressRequest.TargetType.AVOID))
        #        av2 = stub.TargetAddress(MUICore_pb2.AddressRequest(address=addrs[0],type=MUICore_pb2.AddressRequest.TargetType.AVOID))

        sargs = MUICore_pb2.CLIArguments(
            program_path="/home/kok/Desktop/crackme",
            envp=["test1=test2"],
            additional_mcore_args="--core.PORT 3696",
        )
        r = stub.Start(sargs)
        print(r)
        for i in range(10):
            time.sleep(2)
            ml = stub.GetMessageList(r)
            sl = stub.GetStateList(r)
            print(stub.CheckManticoreRunning(r))
            print(ml)
            print(sl)
        r2 = stub.Terminate(r)
        print(r2)


if __name__ == "__main__":
    run()
