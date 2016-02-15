# ParSyn-CEGIS

ParSyn is a flexible software framework for parameter synthesis and repair of cyber-physical systems.

## Requirements

The following software is required in order to use ParSyn-CEGIS

* Python3
* Z3 (version 4.3.1)

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

    $ parsyn-cegis.py benchmarks/thermal1-s2-safe.smt2 "INV_CLK0 INV_CLK1 INV_THETA_M_LO INV_THETA_M_HI" -K 10 -l logs/thermal1-s2-safe.json -t 5
    $ json2tex.py logs/thermal1-s2-safe.json -k 3
