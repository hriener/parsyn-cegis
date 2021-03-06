# ParSyn-CEGIS

ParSyn is a flexible software framework for parameter synthesis and repair of cyber-physical systems.

## Requirements

The following software is required in order to use ParSyn-CEGIS

* Python3
* Z3 (version 4.4.2)

## Executing ParSyn-CEGIS

    $ parsyn-cegis.py --help
    usage: parsyn-cegis.py [-h] [-l [LOG]] [-k [K]] [-K [K]] [-r [{0,1,2,3}]]
                           [-t [T]]
                           smtfile params
                           
      positional arguments:
      smtfile               Input file in SMT-LIB2 format
      params                List of parameters to synthesize
    
    optional arguments:
      -h, --help            show this help message and exit
      -l [LOG], --log [LOG]
                            Log statistics, in JSON format
      -k [K]                Check for k-correctness (default:1)
      -K [K]                Upper bound for k-correctness check
      -r [{0,1,2}]          Counterexample randomization (default:2)
      -t [T]                Repeat experiments (default:1)


A simple example

    $ parsyn-cegis.py benchmarks/thermal1-s2-safe.smt2 "INV_U INV_L" -K 10 -l logs/thermal1-s2-safe.json -t 5
    $ json2tex.py logs/thermal1-s2-safe.json -k 2

## References

Heinz Riener, Robert Könighofer, Görschwin Fey, Roderick Bloem, SMT-Based CPS Parameter Synthesis, In Applied Verification for Continuous and Hybrid Systems (ARCH@CPSWeek 2016), vol 43, pp. 126-133, Vienna, Austra, 2016. ([EasyChair Proc.](https://easychair.org/publications/paper/1fL))
