#!/usr/bin/env python3
################################################################################
# parsyn-cegis.py                                                              #
################################################################################
#                                                                              #
# Author : Heinz Riener (2016)                                                 #
#          Robert Koenighofer (2016)                                           #
#                                                                              #
################################################################################

import argparse
import random
import sexpr
import sys
import time
from subprocess import Popen, PIPE
import statistics
import datetime
import json

RESTART_THRESHOLD = 16

def SMTsolve(smt,params,filename='/tmp/parsyn-cegis.smt2'):
    smt.append('(check-sat-using (par-or (using-params smt :random-seed 10) (using-params smt :random-seed 100) (using-params smt :random-seed 1000)))')
    for p in params:
        smt.append('(get-value ({0}))'.format(p))
    with open(filename, "w") as f:
        f.write("\n".join(smt))
    p = Popen(['z3', '-smt2', filename], stdin=PIPE, stdout=PIPE, stderr=PIPE)
    output, err = p.communicate(b"")
    rc = p.returncode
    #assert rc == 0 # should be 0, but doesn't hv anything to do with sat/unsat/unknown
    if err != b'':
        print(err.decode('utf-8'))
        assert False
    output = output.decode('utf-8').split('\n')
    # print('SMT solver says:','\n'.join(output))
    model = {}
    for i in range(1,len(output)-1):
        key, value = output[i][2:-2].split(' ',1)
        model[key] = value
        #model.append(output[i][2:-2].split(' ',1))
    return (output[0] == 'sat'), model

SMTsolve.counter = 0

def build_correctness_formula(k):
    assert k > 0
    input_arguments = " ".join(["(i{0} input)".format(j) for j in range(0,k)])
    state_definition = " ".join(["  (let ((s{1} (tau s{0} i{0})))".format(j,j+1) for j in range(0,k)])
    safety_induction = ('\n' + ' '*6).join(["(=> (inv s0) (safe s{0}))".format(j) for j in range(0,k)])
    invariants = " ".join(["(inv s{0})".format(j) for j in range(1,k+1)])
    let_close = ")" * k
    return '''
;; {0}-correctness check
(define-fun correct{0} ((s0 state) {1}) Bool
{2}
    (and
      (=> (init s0) (inv s0))
      {3}
      (=> (inv s0) (or {4}))
    )
  {5}
)
    '''.format(k,input_arguments,state_definition,safety_induction,invariants,let_close)

def randomize_if_necessary(s):
    # lazily guess the type of the expression
    if isinstance(s, list):
        for e in s[1:]:
            ok, value = randomize_if_necessary(e)
            if ok:
                return True, value
        return False, value

    try:
        int_value = int(s) # try to cast
        return True, str(random.randint(-1000000,1000000))
    except ValueError:
        pass

    try:
        float_value = float(s) # try to cast
        return True, '{:f}'.format(random.uniform(-1000000.0,1000000.0))
    except ValueError:
        pass

    return False, s

def eval_expression(s):
    if isinstance(s, list):
        args = []
        for e in s[1:]:
            ok, value = eval_expression(e)
            if ok:
                args.append(value)

        if s[0] == '/':
            assert len(args) == 2
            return True, args[0] / args[1]
        elif s[0] == '-':
            assert len(args) == 1
            return True, -args[0]

        return False, s

    try:
        return True, int(s) # try to cast
    except ValueError:
        pass

    try:
        return True, float(s) # try to cast
    except ValueError:
        pass

    return False, s

def cegis(smt, params, k, r, statistics = {}):
    global RESTART_THRESHOLD
    print('===== CEGIS[k={0},r={1}] ====='.format(k,r))

    ### Initial values for statistics
    statistics['time'] = 0
    statistics['#smt_calls'] = 0
    statistics['#restarts'] = 0
    statistics['#parameter_candidates'] = 0
    statistics['parameter_synthesis.time'] = []
    statistics['parameter_synthesis.model'] = []
    statistics['#counterexamples'] = 0
    statistics['correctness_check.time'] = []
    statistics['correctness_check.model'] = []
    statistics['#randomizations'] = 0
    statistics['counterexample_randomization.time'] = []
    statistics['counterexample_randomization.model'] = []

    total_time_start = time.time()

    ### Build correctness formula
    init_smt = (smt + build_correctness_formula(k)).format(*params).split('\n')

    ### Remove parameters from SMT instance
    prepared_smt = []
    for line in init_smt:
        matched = False
        for p in params:
            if line.strip().startswith('(define-fun ' + p):
                a,b,c,d,e = line.split(' ')
                prepared_smt.append('(declare-fun {0} {1} {2})'.format(b,c,d))
                matched = True
        if not matched:
            prepared_smt.append(line)
    init_smt = prepared_smt

    count_no_progress = 0
    while True:
        ### Restart the engine if CEGIS does not make progress
        if r >= 3 and len(statistics['parameter_synthesis.model']) > 1:
            total_progress = 0
            for key in statistics['parameter_synthesis.model'][-2:][0]:
                new_value = sexpr.str2sexpr(statistics['parameter_synthesis.model'][-2:][1][key])
                # print(new_value)
                if isinstance(new_value,list):
                    new_value = new_value[0]
                new_value = eval_expression(new_value)
                old_value = sexpr.str2sexpr(statistics['parameter_synthesis.model'][-2:][0][key])
                # print(old_value)
                if isinstance(old_value,list):
                    old_value = old_value[0]
                old_value = eval_expression(old_value)
                # print(new_value)
                # print(old_value)
                assert new_value[0] == True
                assert old_value[0] == True
                progress = new_value[1] - old_value[1]
                total_progress += abs(progress)
            if total_progress < 0.0000001:
                print("N",end='')
                count_no_progress += 1
            if count_no_progress > 10:
                print("R",end='')
                count_no_progress = 0
                statistics['#restarts'] += 1
                check_smt = list(init_smt)

        ### Restart the engine (and forget all previously learned counterexamples)
        if statistics['#counterexamples'] % RESTART_THRESHOLD == 0:
            print("R",end='')
            statistics['#restarts'] += 1
            RESTART_THRESHOLD += 16*statistics['#restarts']
            check_smt = list(init_smt)
        else:
            # print(statistics['#counterexamples'])
            # print(RESTART_THRESHOLD)
            # print(statistics['#counterexamples'] % RESTART_THRESHOLD == 0)
            print('.',end='')
        sys.stdout.flush()

        ### Compute parameters
        compute_smt = list(check_smt)
        statistics['#smt_calls'] += 1
        statistics['#parameter_candidates'] += 1
        ts = time.time()
        (sat,model) = SMTsolve(compute_smt,params)
        te = time.time()
        statistics['parameter_synthesis.time'].append(te - ts)
        statistics['parameter_synthesis.model'].append(model if sat else {})
        if not sat:
            total_time_end = time.time()
            statistics['cegis.time'] = total_time_end - total_time_start
            return False, {}

        ### Check k-correctness
        correct_smt = []
        for line in check_smt:
            matched = False
            for p in params:
                if line.strip().startswith('(declare-fun ' + p):
                    a,b,c,d = line.split(' ')
                    correct_smt.append('(define-fun {0} {1} {2} {3})'.format(b,c,d[:-1],model[p]))
                    matched = True
            if not matched:
                correct_smt.append(line)
        correct_smt.append('(declare-fun s0 () state)')
        for i in range(0,k):
            correct_smt.append('(declare-fun i{0} () input)'.format(i))
        correct_smt.append('(assert (not (correct{0} s0 {1})))'
                .format(k, ' '.join("i{0}".format(cnt) for cnt in range(0,k))))

        statistics['#smt_calls'] += 1
        statistics['#counterexamples'] += 1
        ts = time.time()
        (sat, cex) = SMTsolve(correct_smt, ['s0'] + ['i{0}'.format(j) for j in range(0,k)])
        te = time.time()
        statistics['correctness_check.time'].append(te - ts)
        statistics['correctness_check.model'].append(cex if sat else {})
        if not sat:
            total_time_end = time.time()
            statistics['cegis.time'] = total_time_end - total_time_start
            return True, model

        ### Make counterexamples as nasty as possible
        if r == 1 or (r >= 2 and statistics['#counterexamples'] % 2 == 0):
            state = sexpr.str2sexpr(cex['s0'])[0][1:]
            for i in range(0,len(state)):
                try_state = []
                for j in range(0,len(state)):
                    if i == j:
                        ok, value = randomize_if_necessary(state[i])
                        try_state.append(value)
                    else:
                        try_state.append(state[j])

                state_sexpr = sexpr.str2sexpr(cex['s0'])[0]
                state_sexpr[1:] = try_state
                if state_sexpr == sexpr.str2sexpr(cex['s0'])[0]:
                    continue # skip the SMT check if no randomization happened
                state_sexpr = sexpr.sexpr2str(state_sexpr)

                nasty_check_smt = list(check_smt)
                nasty_check_smt.append('(assert (not (correct{0} {1} {2})))'
                        .format(k, state_sexpr, " ".join([cex["i" + str(cnt)] for cnt in range(0,k)])))

                statistics['#smt_calls'] += 1
                statistics['#randomizations'] += 1
                ts = time.time()
                (sat, model) = SMTsolve(nasty_check_smt,params)
                te = time.time()
                statistics['counterexample_randomization.time'].append(te - ts)
                statistics['counterexample_randomization.model'].append(cex if sat else {})
                if sat:
                    # print("changed",state[i],"to",try_state[i])
                    state[i] = try_state[i]

            state_sexpr = sexpr.str2sexpr(cex['s0'])[0]
            state_sexpr[1:] = state
            if cex['s0'] != sexpr.sexpr2str(state_sexpr):
                print('G',end='')
            cex['s0'] = sexpr.sexpr2str(state_sexpr)

        ### Make sure that the next parameters are better
        check_smt.append('(assert (correct{0} {1} {2}))'.format(k, cex['s0'], " ".join([cex["i" + str(cnt)] for cnt in range(0,k)])))

###########################################################################
# MAIN
###########################################################################

parser = argparse.ArgumentParser()
parser.add_argument('smtfile', help="Input file in SMT-LIB2 format")
parser.add_argument('params', help="List of parameters to synthesize")
parser.add_argument('-l', '--log', nargs='?', type=argparse.FileType('w'),
                    help='Log statistics, in JSON format')
parser.add_argument('-k', nargs='?', const=1, type=int, default=1,
                    help='Check for k-correctness (default:1)')
parser.add_argument('-K', nargs='?', const=2, type=int,
                    help='Upper bound for k-correctness check')
parser.add_argument('-r', nargs='?', const=3, type=int, default=2, choices=[0,1,2,3],
                    help='Counterexample randomization (default:2)')
parser.add_argument('-t', nargs='?', const=4, type=int, default=1,
                    help='Repeat experiments (default:1)')
args = parser.parse_args()

### Read smt2 file
with open(sys.argv[1]) as f:
    smt = "".join(f.readlines())

### Parameter
params = args.params.split(' ')

### Upper bound for k
if args.K==None:
    args.K = args.k

### Log file
logfile = "None" if args.log == None else args.log.name

def parsyn_cegis(smtfile,params,k,K,r,log):
    global RESTART_THRESHOLD

    ### Print configuration & summary
    print('''
    SMT file: {0}
    Parameter: {1}
    k-Correctness: k = [{2},{3}]
    Counterexample: heuristic = {4}
    '''.format(args.smtfile,params,args.k,args.K,args.r))

    ### CEGIS forall k
    for k in range(args.k,args.K+1):
        RESTART_THRESHOLD = 16
        section = dict()
        section['date'] = str(datetime.datetime.now())
        section['k'] = k

        stats = {}
        (found,values) = cegis(smt,params,k,args.r,stats)

        print('')
        print("#SMT calls:", stats['#smt_calls'])
        print("#restarts:", stats['#restarts'])
        print("#parameter candidates:", stats['#parameter_candidates'])
        print("#counterexamples:", stats['#counterexamples'])
        print("#randomized:", stats['#randomizations'])
        print("time(total): {:8.4f}".format(stats['cegis.time']))
        print("time(param synth): {:8.4f}".format(sum(stats['parameter_synthesis.time']) if len(stats['parameter_synthesis.time']) else 0.0))
        print("time(correct check): {:8.4f}".format(sum(stats['correctness_check.time']) if len(stats['correctness_check.time']) else 0.0))
        print("time(cex random): {:8.4f}".format(sum(stats['counterexample_randomization.time']) if len(stats['counterexample_randomization.time']) else 0.0))
        print("min,avg,max time per param synth: {:8.4f} {:8.4f} {:8.4f}"
              .format(min(stats['parameter_synthesis.time']) if len(stats['parameter_synthesis.time']) else 0.0,
                      statistics.mean(stats['parameter_synthesis.time']) if len(stats['parameter_synthesis.time']) else 0.0,
                      max(stats['parameter_synthesis.time']) if len(stats['parameter_synthesis.time']) else 0.0))
        print("min,avg,max time per correct check: {:8.4f} {:8.4f} {:8.4f}"
              .format(min(stats['correctness_check.time']) if len(stats['correctness_check.time']) else 0.0,
                      statistics.mean(stats['correctness_check.time']) if len(stats['correctness_check.time']) else 0.0,
                      max(stats['correctness_check.time']) if len(stats['correctness_check.time']) else 0.0))
        print("min,avg,max time per cex random: {:8.4f} {:8.4f} {:8.4f}"
              .format(min(stats['counterexample_randomization.time']) if len(stats['counterexample_randomization.time']) else 0.0,
                      statistics.mean(stats['counterexample_randomization.time']) if len(stats['counterexample_randomization.time']) else 0.0,
                      max(stats['counterexample_randomization.time']) if len(stats['counterexample_randomization.time']) else 0.0))
        # print( stats['parameter_synthesis.model'] )
        # print( stats['correctness_check.model'] )
        # print( stats['counterexample_randomization.model'] )

        ### Write statistics to log
        for key in stats:
            section[key] = stats[key]

        if (found):
            print("Found a solution. Parameter values are:")
            for key,value in values.items():
                print("  {0} = {1}".format(key, value))
            section['solution'] = 'Yes'
            log.append(section)
            return 20 # successful -- found a solution
        else:
            section['solution'] = 'No'
            log.append(section)

    print("No solution.")
    return 10 # failed -- no solution


### Write to log
log = []

for i in range(args.t):
    section = dict()
    section['command'] = ' '.join(sys.argv)
    section['date'] = str(datetime.datetime.now())
    section['smt'] = args.smtfile
    section['parameter'] = params
    section['k'] = (args.k,args.K)
    section['r'] = args.r
    log.append(section)

    parsyn_cegis(args.smtfile,params,args.k,args.K,args.r,log)

if args.log != None:
    args.log.write(json.dumps(log, ensure_ascii=False))
