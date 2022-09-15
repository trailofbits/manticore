# Manticore Server
Manticore Server is a gRPC service that acts as a wrapper around  [Manticore](https://github.com/trailofbits/manticore), to support projects like the [Manticore User Interface (MUI)](https://github.com/trailofbits/ManticoreUI). Manticore Server is designed to allow developers to more easily create tools around Manticore that aren't in Python or to allow for Manticore to be run and managed in the cloud/remotely.

# Usage
The Manticore Server can be run via `python3 manticore_server.py` on port `50010`.

Your Manticore Server client will require the relevant gRPC client code. You can find out how to generate gRPC client code in your desired language from [the gRPC website](https://grpc.io/docs/languages/).

You may refer to the [Protobuf Specification](manticore_server/ManticoreServer.proto) for information about the RPC services provided and the message types.
