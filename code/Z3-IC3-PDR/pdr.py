#!/usr/bin/python
# coding=utf-8

# Implementation of the PDR algorithm by Peter Den Hartog. Apr 28, 2016

from z3 import *

# a tcube is a conjunction of literals assosciated with a given frame (t) in the trace
class tCube(object):
    #make a tcube object assosciated with frame t. If t is none, have it be frameless
    def __init__(self, model, lMap, t = None):
        '''
        :param model: s.model() => And(Not(self.post), self.R[-1]) => F[-1] /\ !P
        :param lMap: self.lMap => The string conversion of literals => {str(l):l for l in self.literals}
        :param t: The number of frame
        '''
        self.t = t
        #filter out primed variables when creating cube
        self.cubeLiterals = [lMap[str(l)] == model[l] for l in model if '\'' not in str(l)]
    # return the conjection of all literals in this cube
    def cube(self):
        return And(*self.cubeLiterals)

    def __repr__(self):
        return str(self.t) + ": " + str(sorted(self.cubeLiterals, key=str))


class PDR(object):
    def __init__(self, literals, primes, init, trans, post):
        '''
        :param literals: Boolean Variables
        :param primes: The Post Condition Variable
        :param init: The initial State
        :param trans: Transition Function
        :param post: The Safety Property
        '''
        self.ignore = 0
        self.init = init
        self.trans = trans
        self.literals = literals
        self.lMap = {str(l):l for l in self.literals}
        self.post = post
        self.R = []
        self.primeMap = zip(literals, primes) #F[k] and F[k+1]

    def run(self):
        self.R = list()
        self.R.append(self.init)

        while(1==1):
            #print "The frame:", self.R
            c = self.getBadCube() #
            if(c != None):
                print "Found bad cube:", c
                # we have a bad cube, which we will try to block 
                # if the cube is blocked from the previous frame 
                # we can block it from all previous frames
                #print "Frame is:", self.R
                trace = self.recBlockCube(c)
                if trace != None:
                    print "Found trace ending in bad state:"
                    for f in trace:
                        print f
                    return False
            else: ## found no bad cube, add a new state on to R after checking for induction
                print "Checking for induction"
                inv = self.checkForInduction()
                if inv != None:
                    print "Found inductive invariant:" #, simplify(inv)
                    return True #TODO: Add the process of propagate clause
                print "Did not find invariant, adding frame", len(self.R)
                self.R.append(True) #TODO: Change to append(P) (Check bad state by F[-1] /\ T /\ !P(s')) => Accelerate
                #TODO: Add propagate clause process (pushing lemma?) after append True
            #Lack of PropagateClauses Process, that means the frames could be refine further
    
    # Check all images in R to see if one is inductive  
    def checkForInduction(self):
        for frame in self.R:
            s=Solver()
            s.add(self.trans)
            s.add(frame)
            s.add(Not(substitute(frame, self.primeMap)))
            if s.check() == unsat:
                return frame
        return None

    #loosely based on the recBlockCube method from the berkely paper, without some of the optimizations
    def recBlockCube(self, s0):
        '''
        :param s0: Bad State (generate from tCube class)
        :return: The frames that have been removed bad states
        '''
        Q = []
        Q.append(s0);
        while (len(Q) > 0):
            s = Q[-1] # Take the last bad state
            if (s.t == 0):
                # If a bad cube was not blocked all the way down to R[0]
                # we have found a counterexample and may extract the stack trace
                return Q# CEX found!

            # solve if cube s was blocked by the image of the frame before it
            z = self.solveRelative(s)

            # Can not reach bad state （find a max j satisfies !q indutive relative to F[j])
            if (z == None): # F[i-1] /\ !s /\ T /\ s' -> UNSAT! -> F[i-1] /\ !s /\ T -> !s' -> ADD !s to all frames
                # Cube 's' was blocked by image of predecessor:
                # block cube in all previous frames
                Q.pop() #remove cube s from Q 
                for i in range(1, s.t+1):
                    #if not self.isBlocked(s, i):
                    self.R[i] = And(self.R[i], Not(s.cube())) #This step can add generation step
                    ''' Questions
                    The generalization method:
                    1. Randomly throw literals?
                    2. Find the UNSAT core?
                    3. Not generlization (directly append)
                    4. Using DL to help generlize?
                    5. Any other heuristic methods?
                    '''
            else: # F[i-1] /\ !s /\ T /\ s' -> SAT! (Oh, no) -> F[i-1] /\ !s /\ T -/> !s' -> Some states c can not be transited
                # Some states c cannot be transited from F[i-1] /\ !s to F[i] /\ s
                # Cube 's' was not blocked by image of predecessor
                # it will stay on the stack, and z (the model which allowed transition to s) will we added on top
                Q.append(z) #tCube(model, self.lMap, tcube.t-1) -> Check whether it can be reached or not
                #TODO: Add generalize cube process (or named pushing leamma?)
        return None
    
    #for tcube, check if cube is blocked by R[t-1] AND trans
    def solveRelative(self, tcube):
        '''
        :param tcube:
        :return: model -> The UNSAT core of cube
        self.lmap
        tcude.t -> The number of frame
        '''
        cubeprime = substitute(tcube.cube(), self.primeMap)  # zip(literals, primes) -> F[k] and F[k+1]
        s = Solver()
        s.add(self.R[tcube.t-1]) #F[i-1]
        s.add(self.trans) #T
        s.add(cubeprime)

        #return partial model, in order to create generlized state to block
        if(s.check() != unsat): #cube was not blocked, return new tcube containing the model
            model = s.model() #z3 will return a answer of last check()
            '''Questions
            1. Why this need the partial model? (For block more spaces?)
            2. The other method for generate predecessor?
            '''
            return tCube(model, self.lMap, tcube.t-1) # predecessor c = (i-1,s')

        return None

    #TODO: Add UNSAT core generaliztion to generalize the s.cube()  (which is !q)
    #TODO: Add other heuristic method to drop literal

    # Using the top item in the trace, find a model of a bad state
    # and return a tcube representing it
    # or none if all bad states are blocked
    def getBadCube(self):
        model = And(Not(self.post), self.R[-1])
        #model = And(Not(self.post), T,self.R[-1])
        # The second expression: And(Not(self.post), T /\ self.R[-1])
        s = Solver()
        s.add (model)
        if(s.check() == sat):
            return tCube(s.model(), self.lMap, len(self.R) - 1)
        else:
            # The ans is UNSAT, means F[0] /\ !P is UNSAT
            return None #The first time will return none (when F[0] = I)

    # Is a cube ruled out given the state R[t]?
    def isBlocked(self, tcube, t):
        s = Solver()
        s.add(And(self.R[t], tcube.cube()))
        return s.check() == unsat


    def isInitial(self, cube, initial):
        s = Solver()
        s.add (And(initial, cube))
        return s.check() == sat