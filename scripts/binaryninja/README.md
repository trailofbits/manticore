## Installation

- Symlink the desired plugin into the [plugin directory](https://github.com/Vector35/binaryninja-api/tree/dev/python/examples#loading-plugins)

Example:

```
$ ln -s $PWD/viz.py ~/Library/Application\ Support/Binary\ Ninja/plugins/

```

## Usage

- Run manticore on a binary
- Open the binary in Binary Ninja
- `import` it from the Binary Ninja Script Console, and call desired functions

Example:

```
>>> import viz
>>> viz.viz(bv, '/mnt/hgfs/code/manticore/examples/linux/mcore_1vCAKM')
```
