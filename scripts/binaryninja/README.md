To use a plugin:

1. Symlink the desired plugin into the directory specified here: https://github.com/Vector35/binaryninja-api/tree/dev/python/examples#loading-plugins
2. `import` it from the Binary Ninja Script Console, and call desired functions

Example:

```
$ ln -s $PWD/viz.py ~/Library/Application\ Support/Binary\ Ninja/plugins/

```

From script console:

```
>>> import viz
>>> viz.viz(bv, '/mnt/hgfs/code/manticore/examples/linux/mcore_1vCAKM')
```
