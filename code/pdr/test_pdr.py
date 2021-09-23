from pdr import PDR
from z3 import *
import inspect

def generate_variables(N): return [Bool(chr(ord('a') + i)) for i in range(N)]
def prime(variables): return [Bool(var.__str__() + '\'') for var in variables]
def print_and_write(file, string):
    file.write(string + "\n")
    print string

def verify_program(title, variables, primes, init, trans, post, show_result = True, show_trans = True):
    fname = inspect.stack()[1][3]
    with open(fname + ".out", 'w') as f:
        print_and_write(f, title)
        print_and_write(f, "---------------------------------------")
        print_and_write(f, "Init: " + str(init))
        f.write("Trans: " + str(trans) + "\n")
        if show_trans:
            print "Trans:", trans
        print_and_write(f, "Post:" + str(post))
        pdr = PDR(variables, primes, init, trans, post)
        print
        sat, output = pdr.run()
        res_string = ("SAT\n" if sat else "UNSAT\n") + str(output)
        f.write(res_string + "\n")
        print res_string if show_result else (("SAT\n" if sat else "UNSAT\n") + "Hidden result due to length")
        print
        print

def counter_unsat():
    variables = [BitVec('x', 8)]
    x = variables[0]
    primes = [BitVec('x\'', 8)]
    xp = primes[0]
    verify_program("""Counter (unsatisfiable)
    Adds one to x as long as x < 64. Asserts that x remains less than 10.""",
        variables, primes, And(x == 0), Or(And(xp == x + 1, x < 64), xp == x), x < 10)

def counter_sat():
    variables = [BitVec('x', 5)]
    x = variables[0]
    primes = [BitVec('x\'', 5)]
    xp = primes[0]
    verify_program("""Counter (satisfiable)
    Adds one to x as long as x < 7. Asserts that x remains less than 6.
    x is a 5 bit signed number, so it must only rule out 7 <= x <= 15.""",
        variables, primes, And(x == 0), Or(And(xp == x + 1, x < 6), xp == x), x < 7)

def add_sub_unsat():
    variables = [BitVec('x', 6), BitVec('y', 6)]
    x, y = variables
    primes = [BitVec('x\'', 6), BitVec('y\'', 6)]
    xp, yp = primes
    init = And(x == 4, y == 3)
    trans = And(xp == x + y, yp == x - y)
    post = Not(x == 32)
    verify_program("""Addition and subtraction (unsatisfiable)
    x <- x + y, y <- x - y
    The values of x and y jump around and in frame 6, x = 32""",
        variables, primes, init, trans, post)

def add_sub_sat():
    variables = [BitVec('x', 3), BitVec('y', 3)]
    x, y = variables
    primes = [BitVec('x\'', 3), BitVec('y\'', 3)]
    xp, yp = primes
    init = And(x == 4, y == 3)
    trans = And(xp == x + y, yp == x - y)
    post = Not(x == 2)
    verify_program("""Addition and subtraction (satisfiable)
    x <- x + y, y <- x - y
    The values of x and y jump around, but x can never hold the value 2""",
        variables, primes, init, trans, post)

def shifter_unsat():
    variables = generate_variables(4)
    primes = prime(variables)
    init = And(*[var == False for var in variables[1:]])
    trans = And(*[primes[i] == variables[i - 1] for i in range(len(variables))])
    post = variables[-1] == False
    verify_program("""Shifter (unsatisfiable)
        Starting with all but the LSB False, can the MSB remain False?""",
        variables, primes, init, trans, post)

def shifter_sat():
    variables = generate_variables(4)
    primes = prime(variables)
    init = variables[0]
    trans = And(*[primes[i] == variables[i - 1] for i in range(len(variables))])
    post = Or(*[var for var in variables])
    verify_program("""Shifter (satisfiable)
    Starting with the LSB set to True, maintain at least one bit True""",
        variables, primes, init, trans, post)

def lights_out_sat():
    LEN = 9
    variables = generate_variables(LEN)
    primes = prime(variables)
    on_bits = [0,1,2,5,6,7,8]
    init = And(*([variables[i] for i in on_bits] + [Not(variable) for i, variable in enumerate(variables) if not i in on_bits]))
    trans = Or([And(*[
        (primes+primes)[j] == Not((variables+variables)[j]) if abs(j-i) <= 1 or abs(j-i) == LEN-1 else
        (primes+primes)[j] == (variables+variables)[j] for j in range(LEN)]) for i in range(LEN)])
    post = Or(*[var for var in variables])
    verify_program(
        """Lights out (satisfiable)
    Each step in the program represents a move of inverting a bit and its neighboring bits.
    For it to be unsolvable, neighboring bits must include wrapping around.
    Returning SAT means there is no solution to the starting conditions resulting in turning off all the bits.""",
        variables, primes, init, trans, post, False, False)

def lights_out_unsat():
    LEN = 9
    variables = generate_variables(LEN)
    primes = prime(variables)
    on_bits = [0,1,2,5,6,7,8]
    init = And(*([variables[i] for i in on_bits] + [Not(variable) for i, variable in enumerate(variables) if not i in on_bits]))
    trans = Or([And(*[
        (primes+primes)[j] == Not((variables+variables)[j]) if abs(j-i) <= 1 else
        (primes+primes)[j] == (variables+variables)[j] for j in range(LEN)]) for i in range(LEN)])
    post = Or(*[var for var in variables])
    verify_program(
        """Lights out (unsatisfiable)
    Each step in the program represents a move of inverting a bit and its neighboring bits.
    In this version neighboring bits do not wrap around.
    Returning UNSAT means there is a solution to the starting conditions resulting in turning off all the bits.""",
        variables, primes, init, trans, post, show_trans = False)

def run_all():
    [test() for test in tests[1:]]
tests = [run_all, counter_sat, counter_unsat, shifter_sat, shifter_unsat, add_sub_sat, add_sub_unsat, lights_out_sat, lights_out_unsat]
if __name__ == "__main__":
    test_lookup = {test.__name__: test for test in tests}
    if len(sys.argv) != 2:
        print "Usage: python test_pdy.py [", ", ".join([test.__name__ for test in tests]), "]"
        exit()

    test_lookup[sys.argv[1]]()