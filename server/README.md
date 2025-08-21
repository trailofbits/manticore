# Manticore Server
Manticore Server is a gRPC service that acts as a wrapper around  [Manticore](https://github.com/trailofbits/manticore), to support projects like the [Manticore User Interface (MUI)](https://github.com/trailofbits/ManticoreUI). Manticore Server is designed to allow developers to more easily create tools around Manticore that aren't in Python or to allow for Manticore to be run and managed in the cloud/remotely.

❗NOTE❗: The server is not published or packaged anywhere and is intended to be installed from source in a clean Python virtual environment. The server is only tested for compatibility with the version of Manticore living in the parent directory; this version of Manticore is installed when installing the server.

# Usage
Create a new Python virtual environment:

```bash
python3 -m venv venv
source venv/bin/activate
```

Install the server with `pip install .`. This will install Manticore from the parent directory.

The Manticore Server can be run via `manticore_server`, and it will run on port `50010`.

Your Manticore Server client will require the relevant gRPC client code. You can find out how to generate gRPC client code in your desired language from [the gRPC website](https://grpc.io/docs/languages/).

You may refer to the [Protobuf Specification](manticore_server/ManticoreServer.proto) for information about the RPC services provided and the message types.
