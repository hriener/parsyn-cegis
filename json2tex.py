#!/usr/bin/env python3
################################################################################
# json2tex.py                                                                  #
################################################################################
#                                                                              #
# Author : Heinz Riener (2016)                                                 #
#                                                                              #
################################################################################

import argparse
import json
import statistics

def slice_log(filename, chunk_size):
    data = json.load(open(filename))
    num_slices = int((len(data) - 1) / chunk_size)
    return [data[i*chunk_size:(i*chunk_size)+chunk_size] for i in range(num_slices)]

def mean(list):
    return statistics.mean(list) if len(list) > 0 else 0.0

parser = argparse.ArgumentParser()
parser.add_argument('log', help="Log file in JSON format")
parser.add_argument('-k', help='Maximum k', type=int)
args = parser.parse_args()

data = slice_log(args.log,args.k+1) # max{ k } + 1
num_experiments = len(data)

# for i in range(1,len(data[0])):
#     print("===========================================================================")
#     print(data[0][0]['command'])
#     print('k:',data[0][i]['k'])
#     print('#SMT calls: {:8.2f}'.format(mean([data[l][i]['#smt_calls'] for l in range(num_experiments)])))
#     print('#restarts: {:8.2f}'.format(mean([data[l][i]['#restarts'] for l in range(num_experiments)])))
#     print('#counterexamples: {:8.2f}'.format(mean([data[l][i]['#counterexamples'] for l in range(num_experiments)])))
#     print('#parameter candidates: {:8.2f}'.format(mean([data[l][i]['#parameter_candidates'] for l in range(num_experiments)])))
#     print('#cex randomizations: {:8.2f}'.format(mean([data[l][i]['#randomizations'] for l in range(num_experiments)])))
#
#     print('time[total]: {:8.2f}'.format(mean([data[l][i]['cegis.time'] for l in range(num_experiments)])))
#     print('time[param synth]: {:8.2f}'.format(mean([sum(data[l][i]['parameter_synthesis.time']) for l in range(num_experiments)])))
#     print('time[correct check]: {:8.2f}'.format(mean([sum(data[l][i]['correctness_check.time']) for l in range(num_experiments)])))
#     print('time[cex random]: {:8.2f}'.format(mean([sum(data[l][i]['counterexample_randomization.time']) for l in range(num_experiments)])))
#     print('time per param synth: {:8.2f}'.format(mean([mean(data[l][i]['parameter_synthesis.time']) for l in range(num_experiments)])))
#     print('time per correct check: {:8.2f}'.format(mean([mean(data[l][i]['correctness_check.time']) for l in range(num_experiments)])))
#     print('time per cex random: {:8.2f}'.format(mean([mean(data[l][i]['counterexample_randomization.time']) for l in range(num_experiments)])))

for i in range(1,len(data[0])):
    name, ext = data[0][0]['smt'].split('/')[-1:][0].split('.')
    num_params = len(data[0][0]['parameter'])
    k = data[0][i]['k']
    smt_calls = mean([data[l][i]['#smt_calls'] for l in range(num_experiments)])
    num_cex = mean([data[l][i]['#counterexamples'] for l in range(num_experiments)])
    solution = data[0][i]['solution']
    tp = mean([sum(data[l][i]['parameter_synthesis.time']) for l in range(num_experiments)])
    tc = mean([sum(data[l][i]['correctness_check.time']) for l in range(num_experiments)])
    tr = mean([sum(data[l][i]['counterexample_randomization.time']) for l in range(num_experiments)])
    time = mean([data[l][i]['cegis.time'] for l in range(num_experiments)])

    print('\\texttt{{{:s}}} & {:d} & {:d} & {:8.2f} & {:8.2f} & {:3s} & {:8.2f} & {:8.2f} & {:8.2f} & {:8.2f}\\\\'.format(name,num_params,k,smt_calls,num_cex,solution,tp,tc,tr,time))
