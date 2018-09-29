## Installation

- Symlink the desired plugin into the [plugin directory](https://github.com/Vector35/binaryninja-api/tree/dev/python/examples#loading-plugins)

Example:

```
## Installation:
Copy and paste the `manticore_viz` directory to the binary ninja [plugin folder](https://github.com/Vector35/binaryninja-api/tree/dev/python/examples#loading-plugins).


Alternatively, you can create a symbolic link to the respective directories.
E.g., in Mac OS X
```
cd ~/Library/Application\ Support/Binary\ Ninja
ln -s <manticore_root>/scripts/binaryninja/manticore_viz .
```

## Usage

- Run Manticore on a binary
- Open the same binary in Binary Ninja
- Select "Highlight Trace"
