from z3 import *

#This helper class specifies a cube and a frame
#in which it is reachable.
class Cube(object):
    def __init__(self, model, variable_lookup, i = None):
        self.values = [simplify(variable_lookup[str(v)] == model[v]) for v in model if str(v) in variable_lookup]
        self.i = i

    @property
    def cube(self):
        return And(*self.values)

    @property
    def not_cube(self):
        return Or(*[Not(value) for value in self.values])

    def __repr__(self):
        return "{" + ("" if self.i == None else str(self.i) + ": ") + str(self.values) + "}"

class StackFrame(object):
    def __init__(self, *cubes):
        self.cubes = list(cubes)
        self.expression = And(*cubes)
    def add_cube(self, cube):
        self.cubes.append(cube)
        self.expression = And(*self.cubes)

class PDR(object):    
    def __init__(self, variables, primes, init, trans, post):
        self.variables = variables
        self.variable_dict = {str(v): v for v in self.variables}
        self.primes = primes
        self.vTOp = zip(variables, primes)
        self.init = init
        self.trans = trans
        self.post = post

        self.stack_frames = [StackFrame(init)]
        self.stack_trace = []

    #Finds a cube in ~post and the latest frame
    def getBadCube(self):
        s = Solver()
        s.add(And(Not(self.post), self.stack_frames[self.N].expression))
        if s.check() == sat:
            return Cube(s.model(), self.variable_dict, self.N)
        return None

    def newFrame(self):
        print self.N,
        sys.stdout.flush()
        self.stack_frames.append(StackFrame())

    #Checks whether a cube has been entirely blocked
    #in the given frame, only for performance
    def isBlocked(self, cube, i):
        s = Solver()
        s.add(And(self.stack_frames[i].expression, cube))
        return s.check() == unsat

    #Tries to find a cube in the previous frame that would
    #reach the given cube
    def solveRelative(self, cube):
        cubePrime = substitute(cube.cube, self.vTOp)
        s = Solver()
        s.add(self.stack_frames[cube.i - 1].expression)
        s.add(self.trans)
        s.add(cubePrime)
        if s.check() == unsat:
            return None
        return s.model()

    #Checks whether the we have found an inductive invariant
    def induct(self):
        for i, frame in enumerate(self.stack_frames[:-1]):
            check_frame = frame.expression
            s = Solver()
            s.add(And(self.trans, check_frame, 
                Not(substitute(check_frame, self.vTOp))))
            invariant = s.check() == unsat
            if invariant:
                return check_frame
        return None

    #Attemps to block a cube recursively
    #Returns None if the cube was able to be blocked
    #Returns a stack trace if the cube cannot be blocked
    def blockCube(self, cube):
        #If solution is for frame 0, we have found a stack trace reaching ~post
        if cube.i == 0:
            return [cube]
        while True:
            assert(not self.isBlocked(cube.cube, cube.i))
            solution = self.solveRelative(cube)
            #The cube is found to be unreachable by the previous frame
            if solution == None:
                #Block it in the frame it is found in and all previous frames
                for i in range(1, cube.i + 1):
                    if not self.isBlocked(cube.cube, i):
                        self.stack_frames[i].add_cube(simplify(cube.not_cube))
                return None
            #The cube is found to be reachable by the previous frame
            else:
                candidate = {v: solution[v] for v in solution if str(v) in self.variable_dict}
                candidateCube = Cube(candidate, self.variable_dict, cube.i - 1)
                #Attempt to block this new candidate as well
                trace = self.blockCube(candidateCube)
                if trace:
                    return trace + [cube]
        return None

    #Main entry point of PDR
    def run(self):
        print "Current frame",
        self.newFrame()
        while True:
            cube = self.getBadCube()
            if cube:
                trace = self.blockCube(cube)
                if trace != None:
                    return False, trace
            else:
                invarient = self.induct()
                if invarient:
                    return True, invarient
                self.newFrame()

    @property
    def N(self):
        return len(self.stack_frames) - 1
