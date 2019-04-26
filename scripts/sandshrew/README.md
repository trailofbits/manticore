# sandshrew

sandshrew is a prototype concolic unit testing tool for cryptographic verification. It harnesses the [Manticore](https://github.com/trailofbits/manticore) API in order to perform unconstrained concolic execution on C cryptographic primitives.

> Read more: https://blog.trailofbits.com/2019/04/01/performing-concolic-execution-on-cryptographic-primitives/

## Usage

```
$ python sandshrew.py -h
usage: sandshrew [-h] -t TEST [-c CONSTRAINT] [--debug] [--trace]
                 [--no-concolic] [--cmpsym CMP_SYM]

optional arguments:
  -h, --help            show this help message and exit
  -c CONSTRAINT, --constraint CONSTRAINT
                        Constraint to apply to symbolic input. Includes ascii,
                        alpha, num, or alphanum
  --debug               If set, turns on debugging output for sandshrew
  --trace               If set, trace instruction recording will be outputted
                        to logger
  --cmpsym CMP_SYM      Overrides comparison function used to test for
                        equivalence (default is strcmp)

required arguments:
  -t TEST, --test TEST  Target binary for sandshrew analysis
```

## Example

To run the sandshrew script against a sample cryptographic hash collision test case:

```
cd examples/
make & cd ..
python sandshrew.py --test examples/test_openssl_md5 --debug
```

![sandshrewgif](https://trailofbits.files.wordpress.com/2019/04/237667.cast_.gif)

