from z3 import *


# conjunction of literals.
class tCube:
    # make a tcube object assosciated with frame t.
    def __init__(self, t=0):
        self.t = t
        self.cubeLiterals = list()

    # 解析 sat 求解出的 model, 并将其加入到当前 tCube 中
    def addModel(self, lMap, model):
        no_primes = [l for l in model if str(l)[-1] != '\'']
        no_input = [l for l in no_primes if str(l)[0] != 'i']
        self.add(simplify(And([lMap[str(l)] == model[l] for l in no_input])))

    # 扩增 CNF 式
    def addAnds(self, ms):
        for i in ms:
            self.add(i)

    # 增加一个公式到当前 tCube() 中
    def add(self, m):
        g = Goal()
        g.add(m)
        t = Tactic('tseitin-cnf')  # 转化得到该公式的 CNF 范式
        for c in t(g)[0]:
            self.cubeLiterals.append(c)
        if len(t(g)[0]) == 0:
            self.cubeLiterals.append(True)

    # 删除第 i 个元素，并返回 tCube
    def delete(self, i: int):
        res = tCube(self.t)
        for it, v in enumerate(self.cubeLiterals):
            if i == it:
                res.add(True)
                continue
            res.add(v)
        return res

    def cube(self):
        return simplify(And(self.cubeLiterals))

    def __repr__(self):
        return str(self.t) + ": " + str(sorted(self.cubeLiterals, key=str))


# class tClause:
#     def __init__(self, t=0):
#         self.t = t
#         self.clauseLiterals = []
#
#     def defFromNotCube(self, c: tCube):
#         for cube in c.cubeLiterals:
#             self.clauseLiterals.append(Not(cube))
#
#     def clause(self):
#         return simplify(Or(self.clauseLiterals))
#
#     def add(self, m):
#         self.clauseLiterals.append(m)
#
#     def delete(self, i: int):
#         res = tClause(self.t)
#         for it in range(len(self.clauseLiterals)):
#             if it == i:
#                 continue
#             res.add(self.clauseLiterals[it])
#         return res
#
#     def __repr__(self):
#         return str(self.t) + ": " + str(sorted(self.clauseLiterals, key=str))


class PDR:
    def __init__(self, primary_inputs, literals, primes, init, trans, post):
        self.primary_inputs = primary_inputs
        self.init = init
        self.trans = trans
        self.literals = literals
        self.items = self.primary_inputs + self.literals
        self.lMap = {str(l): l for l in self.items}
        self.post = post
        self.frames = list()
        self.primeMap = [(literals[i], primes[i]) for i in range(len(literals))]
        # print("init:")
        # print(self.init.cube())
        # print("trans...")
        # print(self.trans.cube())
        # print("post:")
        # print(self.post.cube())

    def run(self):
        self.frames = list()
        self.frames.append(self.init)

        while True:
            c = self.getBadCube()
            if c is not None:
                # print("get bad cube!")
                trace = self.recBlockCube(c)
                if trace is not None:
                    print("Found trace ending in bad state:")
                    for f in trace:
                        print(f)
                    return False
                print("recBlockCube Ok! F:")
                for i in self.frames:
                    print(i)
            else:
                print("Adding frame " + str(len(self.frames)) + "...")
                self.frames.append(tCube(len(self.frames)))
                for index, fi in enumerate(self.frames):
                    if index == len(self.frames) - 1:
                        break
                    for c in fi.cubeLiterals:
                        s = Solver()
                        s.add(fi.cube())
                        s.add(self.trans.cube())
                        s.add(Not(substitute(c, self.primeMap)))  # F[i] and T and Not(c)'
                        if s.check() == unsat:
                            self.frames[index + 1].add(c)
                    if self.checkForInduction(fi):
                        print("Fond inductive invariant:\n" + str(fi.cube()))
                        return True
                print("New Frame " + str(len(self.frames) - 1) + ": ")
                print(self.frames[-1].cube())

    def checkForInduction(self, frame):
        print("check for Induction now...")
        s = Solver()
        s.add(self.trans.cube())
        s.add(frame.cube())
        s.add(Not(substitute(frame.cube(), self.primeMap)))  # T and F[i] and Not(F[i])'
        if s.check() == unsat:
            return True
        return False

    def recBlockCube(self, s0: tCube):
        print("recBlockCube now...")
        Q = [s0]
        while len(Q) > 0:
            s = Q[-1]
            if s.t == 0:
                return Q
            z = self.solveRelative(s)
            if z is None:
                Q.pop()
                s = self.MIC(s)
                for i in range(1, s.t + 1):
                    self.frames[i].add(Not(s.cube()))
            else:
                Q.append(z)
        return None

    def MIC(self, q: tCube):
        for i in range(len(q.cubeLiterals)):
            q1 = q.delete(i)
            if self.down(q1):
                q = q1
        return q
        # i = 0
        # while True:
        #     print(i)
        #     if i < len(q.cubeLiterals) - 1:
        #         i += 1
        #     else:
        #         break
        #     q1 = q.delete(i)
        #     if self.down(q1):
        #         q = q1
        # return q

    def down(self, q: tCube):
        while True:
            s = Solver()
            s.push()
            s.add(And(self.frames[0].cube(), Not(q.cube())))
            if unsat == s.check():
                return False
            s.pop()
            s.push()
            s.add(And(self.frames[q.t].cube(), Not(q.cube()), self.trans.cube(),
                      substitute(q.cube(), self.primeMap)))  # Fi and not(q) and T and q'
            if unsat == s.check():
                return True
            # m = s.model()
            # q.addModel(self.lMap, m)
            # s.pop()
            return False

    # def tcgMIC(self, q: tCube, d: int):
    #     for i in range(len(q.cubeLiterals)):
    #         q1 = q.delete(i)
    #         if self.ctgDown(q1, d):
    #             q = q1
    #     return q
    #
    # def ctgDown(self, q: tCube, d: int):
    #     ctgs = 0
    #     while True:
    #         s = Solver()
    #         s.push()
    #         s.add(And(self.R[0].cube(), Not(q.cube())))
    #         if unsat == s.check():
    #             return False
    #         s.pop()
    #         s.push()
    #         s.add(And(self.R[q.t].cube(), Not(q.cube()), self.trans.cube(),
    #                   substitute(q.cube(), self.primeMap)))  # Fi and not(q) and T and q'
    #         if unsat == s.check():
    #             return True
    #         m = s.model()

    # tcube is bad state
    def solveRelative(self, tcube):
        cubePrime = substitute(tcube.cube(), self.primeMap)
        s = Solver()
        s.add(self.frames[tcube.t - 1].cube())
        s.add(self.trans.cube())
        s.add(Not(tcube.cube()))
        s.add(cubePrime)  # F[i - 1] and T and Not(badCube) and badCube'
        if s.check() == sat:
            model = s.model()
            c = tCube(tcube.t - 1)
            c.addModel(self.lMap, model)  # c = sat_model
            return c
        return None

    def getBadCube(self):
        print("seek for bad cube...")
        model = And(Not(self.post.cube()), self.frames[-1].cube())  # F[k] and Not(p)
        s = Solver()
        s.add(model)
        if s.check() == sat:
            res = tCube(len(self.frames) - 1)
            res.addModel(self.lMap, s.model())  # res = sat_model
            print("get bad cube:")
            print(res.cube())
            return res
        else:
            return None


if __name__ == '__main__':
    pass
