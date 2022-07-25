from PyMiniSolvers import minisolvers
from z3 import *


# def s1():
#     s = Solver()
#     f = Function('f', IntSort(), IntSort(), IntSort())
#     a = Int('a')
#     b = Int('b')
#     x = Int('x')
#     s.add(ForAll(x, f(x, x) >= x + a))
#     s.add(f(a, b) < a)
#     s.add(a > 0)
#     if s.check() == sat:
#         print(s.model())
#         for l in s.model():
#             print(s.model()[l])
#
#
# def s2():
#     s = Solver()
#     x = Int('x')
#     y = Int('y')
#     a1 = Array('a1', IntSort(), IntSort())
#     s.add(Select(a1, x) == x)
#     s.add(Store(a1, x, y) == a1)
#     s.add(is_not(x == y))
#     if s.check() == sat:
#         print(s.model())
#     else:
#         print("unsat")
#
#
# def z3ToCNF():
#     x = Bool('x')
#     y = Bool('y')
#     z = Bool('z')
#     s = Or(And(x, y), z)
#     g = Goal()
#     g.add(s)
#     # describe_tactics()
#     t = Tactic('tseitin-cnf')
#     print(t(g))
#     s = Solver()
#     s.add(t(g)[0])
#
#
# def Mutual():
#     # Try:n[i] == state.T
#     # Crit:And(n[i] == state.C,Not(x))
#     # Exit:n[i]==state.E
#     # Idle:And(n[i]==state.I,x)
#     state = Datatype('state')
#     state.declare('I')
#     state.declare('T')
#     state.declare('C')
#     state.declare('E')
#     state = state.create()
#     n = Array('n', IntSort(), state)
#     x = Bool('x')
#     i = Int('i')
#     j = Int('j')
#     k = Int('k')
#     np = Array('n\'', IntSort(), state)
#     xp = Bool('x\'')
#     ip = Int('i\'')
#     jp = Int('j\'')
#     kp = Int('k\'')
#     variables = [i, j, k, x, n]
#     primes = [ip, jp, kp, xp, np]
#     init = And(n[i] == state.I, n[j] == state.I, x)
#     # trans = Or(Implies(And(n[i] == state.I, x), np[ip] == state.T), Implies(And(n[j] == state.I, x), np[jp] ==
#     # state.T), Implies(And(n[k] == state.I, x), np[kp] == state.T), Implies(And(n[i] == state.T, x), And(np[ip] ==
#     # state.C, xp == Not(x))), Implies(And(n[j] == state.T, x), And(np[jp] == state.C, xp == Not(x))), Implies(And(n[
#     # k] == state.T, x), And(n[k] == state.C, xp == Not(x))), Implies(n[i] == state.C, np[ip] == state.E),
#     # Implies(n[j] == state.C, np[jp] == state.E), Implies(n[k] == state.C, np[kp] == state.E), Implies(n[i] ==
#     # state.E, And(np[ip] == state.I, xp == x)), Implies(n[j] == state.E, And(np[jp] == state.I, xp == x)),
#     # Implies(n[k] == state.E, And(np[kp] == state.I, xp == x)))
#     trans = And(np[ip] == state.C, xp == Not(x))
#     post = Implies(n[i] == state.C, n[j] != state.C)
#     return variables, primes, init, trans, post

def miniSatUse():
    S = minisolvers.MinisatSolver()
    for i in range(3):
        S.new_var()
    for clause in [1], [-1, 2], [-1, 2, 3], [1], [1]:
        S.add_clause(clause)
    while S.solve():
        print(list(S.get_model()))
        S.block_model()



def z3Use():
    a = Bool("a")
    b = Bool("b")
    s = Solver()
    s.add(And(a, b))
    while sat == s.check():
        print(s.model())
        print(type(s.model()))


if __name__ == '__main__':
    a = [1, 2]
    b = a.copy()
    b.append(3)
    print(a)
