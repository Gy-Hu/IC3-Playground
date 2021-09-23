from pysmt.shortcuts import Symbol, Not, And, Or, Implies, Ite, BVAdd, BV, EqualsOrIff, BVNot, BVSub
from pysmt.shortcuts import is_sat, is_unsat, Solver, TRUE
from pysmt.typing import BOOL, BVType
from pysmt.shortcuts import Interpolator, simplify
from pysmt.logics import QF_BV

from utilfunc import _get_var, _get_cubes_with_more_var, _get_cubes_with_fewer_var
from cegpbe import CexGuidedPBE
from opextract import OpExtractor
from sts import TransitionSystem

import heapq


#----------- Basic Parameters -------------------
Config_Max_Frame = 10000000
Config_use_itp_in_pushing = False
Config_analyze_use_itp_in_pushing = True
Config_debug = True
Config_partial_model = True
Config_simplify_itp = True
Config_rm_cex_in_prev = True
#----------- Heuristics -------------------
Config_enhance_giveup_threshold = (2, 3) # (8,10)
Config_cex_invalid_itp_guess_threshold = (4,5) # (18, 20)
Config_try_drop_cex = (5,5) # (30, 50)  # after 30 frames, per 50
#----------- NEEDS EXPERIMENTS -------------------
Config_use_fact_in_sygus = False
Config_strengthen_effort_for_prop = 1e10 # almost infinity (should make it 1000?)


def pause():
    if Config_debug:
        input()



class BaseAddrCnt(TransitionSystem):
    def __init__(self, nbits):
        self.nbits = nbits # save the number of bits
        self.mask = 2**(nbits)-1

        base = Symbol('base', BVType(nbits))
        addr = Symbol('addr', BVType(nbits))
        cnt  = Symbol('cnt',  BVType(nbits))
        inp  = Symbol('inp',  BVType(nbits))
        lden = Symbol('lden',  BVType(1))

        self.base = base 
        self.addr = addr 
        self.cnt  = cnt  
        self.inp  = inp  
        self.lden = lden 


        variables = [base, addr, cnt, inp, lden]
        prime_variables = [TransitionSystem.get_prime(v) for v in variables]
        init = base.Equals(0) & addr.Equals(0) & cnt.Equals(0)
        trans= TransitionSystem.get_prime(base).Equals( \
            Ite(lden.Equals(1), inp, base  )) & \
            TransitionSystem.get_prime(addr).Equals( \
            Ite(lden.Equals(1), inp, BVAdd(addr, BV(1, nbits) ) )) & \
            TransitionSystem.get_prime(cnt).Equals( \
            Ite(lden.Equals(1), BV(0, nbits), BVAdd(cnt, BV(1, nbits) ) ))
            
        TransitionSystem.__init__(self, \
          variables = variables, \
          prime_variables = prime_variables, \
          init = init, trans = trans )

    def neq_property(self, base, addr, cnt):
        addr = addr & self.mask
        base = base & self.mask
        cnt  = cnt  & self.mask

        assert ( addr !=  ((base+cnt) & self.mask) )

        return Not( self.addr.Equals(addr) & self.base.Equals(base) & self.cnt.Equals(cnt) )


class TwoCnt(TransitionSystem):
    def __init__(self, nbits, zero_init = False):
        self.nbits = nbits # save the number of bits
        self.mask = 2**(nbits)-1

        self.c1   = Symbol('c1', BVType(nbits))
        self.c2   = Symbol('c2', BVType(nbits))
        self.inp  = Symbol('inp',  BVType(nbits))
        self.lden = Symbol('lden',  BVType(1))

        variables = [self.c1, self.c2, self.inp, self.lden]
        prime_variables = [TransitionSystem.get_prime(v) for v in variables]
        if zero_init:
            init = self.c1.Equals(0) & self.c2.Equals(self.mask)
        else:
            init = self.c1.Equals(self.inp) & self.c2.Equals(BVNot(self.inp))
        trans= TransitionSystem.get_prime(self.c1).Equals( \
            Ite(self.lden.Equals(1), self.inp, BVAdd(self.c1, BV(1, nbits)  ))) & \
            TransitionSystem.get_prime(self.c2).Equals( \
            Ite(self.lden.Equals(1), BVNot(self.inp), BVSub(self.c2, BV(1, nbits)  )))
            
        TransitionSystem.__init__(self, \
          variables = variables, \
          prime_variables = prime_variables, \
          init = init, trans = trans )

    def neq_property(self, c1, c2):
        c1 = c1 & self.mask
        c2 = c2 & self.mask

        assert ( c1 + c2 != self.mask)

        return Not( self.c1.Equals(c1) & self.c2.Equals(c2) )

    def false_property(self, c1, c2):
        c1 = c1 & self.mask
        c2 = c2 & self.mask

        assert ( c1 + c2 == self.mask)

        return Not( self.c1.Equals(c1) & self.c2.Equals(c2) )


class TwoCntNoload(TransitionSystem):
    def __init__(self, nbits, zero_init = False):
        self.nbits = nbits # save the number of bits
        self.mask = 2**(nbits)-1

        self.c1   = Symbol('c1', BVType(nbits))
        self.c2   = Symbol('c2', BVType(nbits))
        self.inp  = Symbol('inp',  BVType(nbits))

        variables = [self.c1, self.c2, self.inp]
        prime_variables = [TransitionSystem.get_prime(v) for v in variables]
        if zero_init:
            init = self.c1.Equals(0) & self.c2.Equals(self.mask)
        else:
            init = self.c1.Equals(self.inp) & self.c2.Equals(BVNot(self.inp))
        trans= TransitionSystem.get_prime(self.c1).Equals( \
            BVAdd(self.c1, BV(1, nbits)  )) & \
            TransitionSystem.get_prime(self.c2).Equals( \
            BVSub(self.c2, BV(1, nbits)  ))
            
        TransitionSystem.__init__(self, \
          variables = variables, \
          prime_variables = prime_variables, \
          init = init, trans = trans )

    def neq_property(self, c1, c2):
        c1 = c1 & self.mask
        c2 = c2 & self.mask

        assert ( c1 + c2 != self.mask)

        return Not( self.c1.Equals(c1) & self.c2.Equals(c2) )

    def false_property(self, c1, c2):
        c1 = c1 & self.mask
        c2 = c2 & self.mask

        assert ( c1 + c2 == self.mask)

        return Not( self.c1.Equals(c1) & self.c2.Equals(c2) )

# keep_vars and remove_vars are primal var list/set

def _cube2prop(cube):
  return Not(And([EqualsOrIff(v,val) for v,val in cube]))


class PDR(object):
    def __init__(self, system):
        self.system = system
        self.frames = [ [system.init], []  ] # list of list of clauses
        
        if Config_partial_model:
          self.solver = Solver(name = 'z3') # use z3 for partial model
        else:
          self.solver = Solver()

        self.valid_solver = self.solver # we can use btor later 
        self.itp_solver = Interpolator(logic=QF_BV)
        self.prime_map = dict([(v, TransitionSystem.get_prime(v)) for v in self.system.variables])
        self.primal_map = dict([(TransitionSystem.get_prime(v), v) for v in self.system.variables])
        self.cexs_blocked = {}  # <n, cex> : n -> list of cex, maybe blocked already
        self.unblockable_fact = {} # <n, ex> : n -> list of ex, unblocked, used to syn


        self.frames_pushed_idxs_map = {} # n->idx+1 tried
        self.facts_pushed_idxs_map = {} # n->idx+1 tried

        # map: v --> next_v
        # itp and cex number mapping
        self.lemma_to_cex_map_perframe = {} # <n , <itp_number , set of (cex_number)>>
        self.cex_pushed_status = {} # <n, <map of status: idxs pushed and forward map number, None unable to push, '*subsume*'> >
        self.cex_origin = {} # <n , <cex number, (number/None,'prop', 'push_lemma', 'push_fact' )>>
        self.cex_covered_by_pushed_lemmas =  {} # <n , set of (cex id) >

        # statistics
        self.cex_to_itp_enhance_fail = {}
        self.cex_to_itp_push_fail = {}
        #canonicalize_cex

    def dump_frames(self, toStr = False):
        retS = []
        def _printStr(*argl, **argd):
            if (toStr):
                retS.append( ''.join ( argl ) )
            else:
                print(*argl, **argd)

        _printStr ('---------- Frames DUMP ----------')
        for fidx,f in enumerate(self.frames):
            _printStr ('Frame : %d'%fidx)
            for lidx, lemma in enumerate(f):
                ptr = '*' if self.frames_pushed_idxs_map.get(fidx,0) == lidx else ' '
                blocked_cexsIdx = self.lemma_to_cex_map_perframe.get(fidx, dict()).get(lidx, set())
                _printStr ('  %s l%d: ' % (ptr,lidx) , lemma.serialize(), '| blockes:', str(blocked_cexsIdx))
            if self.frames_pushed_idxs_map.get(fidx,0) == lidx + 1:
                _printStr ('    all tried to push')

            if fidx in self.cexs_blocked:
                _printStr ('  CEX blocked # : %d'% len(self.cexs_blocked[fidx]) , '|  CEX covered : ', str(self.cex_covered_by_pushed_lemmas.get(fidx,set())))
                for cidx, cex in enumerate(self.cexs_blocked[fidx]):
                    ptr = '*' if self.cexs_pushed_idxs_map.get(fidx,0) == cidx else ' '  # push pointer position
                    cvr = '+' if cidx in self.cex_covered_by_pushed_lemmas.get(fidx,set()) else ' ' # covered by pushed lemmas
                    pushed_status_list = self.cex_pushed_status.get(fidx, dict())
                    pushed_status = pushed_status_list[cidx] if cidx < len(pushed_status_list) else 'Unknown'
                    origin = self.cex_origin.get(fidx, dict()).get(cidx, 'Unknown')
                    hashkey = self._canonicalize_cex(cex)
                    itp_push_status = self.cex_to_itp_push_fail.get(hashkey,(0,0))
                    itp_repr_status = self.cex_to_itp_enhance_fail.get(hashkey,(0,0))
                    _printStr ('  %s%s c%d ' % (ptr,cvr, cidx), '|', \
                        str(itp_push_status), str(itp_repr_status), '|:', \
                        self.print_cube(cex), '| PS:', str(pushed_status), '| O:', str(origin))
                if self.cexs_pushed_idxs_map.get(fidx,0) == cidx + 1:
                    _printStr ('    all tried to push')
            if fidx in self.unblockable_fact:
                _printStr ('  facts # : %d'% len(self.unblockable_fact[fidx]) )
                for cidx, fact in enumerate(self.unblockable_fact[fidx]):
                    _printStr ('    f%d: ' % cidx, self.print_cube(fact) )
        _printStr ('---------- END Frames DUMP ----------')
        return '\n'.join(retS)

    def _canonicalize_cex(self, cex):
        """cex to a hashable thing"""
        cex_str = [(v.symbol_name(), val) for v, val in cex ]
        return tuple(sorted(cex_str, key = lambda x: x[0]))

    def _add_cex(self, cex, fidx, origin):
        assert (isinstance(origin, tuple)), "need tuple get : "+str(origin) # must be tuple
        if fidx not in self.cexs_blocked:
            self.cexs_blocked[fidx] = []
        assert (cex not in self.cexs_blocked[fidx])

        if cex not in self.cexs_blocked[fidx]: # do you need check duplicity?
            self.cexs_blocked[fidx].append(cex)
            cexIdx=len(self.cexs_blocked[fidx])-1
        else:
            cexIdx=self.cexs_blocked[fidx].index(cex)

        if fidx not in self.cex_origin:
            self.cex_origin[fidx] = dict()
        if cexIdx not in self.cex_origin[fidx]:
            self.cex_origin[fidx][cexIdx] = origin

        return cexIdx

    def _add_lemma(self, lemma, fidx, cidxs):
        """cidxs should be a set"""
        assert (lemma not in self.frames[fidx])
        if lemma not in self.frames[fidx]:
            self.frames[fidx].append(lemma)
            lidx = len(self.frames[fidx])-1
        else:
            lidx = self.frames[fidx].index(lemma)
        if fidx not in self.lemma_to_cex_map_perframe:
            self.lemma_to_cex_map_perframe[fidx] = dict()
        self.lemma_to_cex_map_perframe[fidx][lidx] = self.lemma_to_cex_map_perframe[fidx].get(lidx, set()).union(cidxs)

    def _add_fact(self, fact, fidx):
        if fidx not in self.unblockable_fact:
            self.unblockable_fact[fidx] = []
        if fact not in self.unblockable_fact[fidx]: # TODO: not efficient
            self.unblockable_fact[fidx].append(fact)

    def _add_lemma_to_all_prev_frame(self, end_frame_id, lemma):
        for idx in range(1,end_frame_id+1):
            if lemma not in self.frames[idx]:
                self.frames[idx].insert(0, lemma)
                pushed_idx = self.frames_pushed_idxs_map.get(idx, 0)
                pushed_idx += 1
                self.frames_pushed_idxs_map[idx] = pushed_idx
                # fix the lemma_to_cex_map_perframe
                lidx_to_cidxs_map = list(self.lemma_to_cex_map_perframe.get(idx, dict()).items())
                self.lemma_to_cex_map_perframe[idx] = dict()
                for lidx, cidxs in lidx_to_cidxs_map:
                    self.lemma_to_cex_map_perframe[idx][lidx+1] = cidxs


    def check_init_failed(self, prop, remove_vars, keep_vars):
        init_cex = self.solve(self.frames[0] + [ Not(prop) ] )
        print ("[Checking init] F0 and not P")
        if init_cex is not None:
            print("[Checking init] Property failed at INIT")
            print("[Checking init] CEX: ", self.print_cube(init_cex))
            return True
        print ("[Checking init]  F0 and T and not P'")
        init_cex = self.get_bad_state_from_property_invalid_after_trans(
            prop = prop, idx = 0, use_init = True, remove_vars = remove_vars, keep_vars = keep_vars)
        if init_cex is not None:
            print("[Checking init] Property failed at F1")
            print("[Checking init] CEX @F0: ", self.print_cube(init_cex))
            return True
        print ("[Checking init] Done")
        return False



    def check_property(self, prop, remove_vars = [], keep_vars = None):
        """Property Directed Reachability approach without optimizations."""
        print("[Checking property] Property: %s." % prop)

        if self.check_init_failed(prop, remove_vars, keep_vars):
            return False

        self._add_lemma(fidx = 1, cidxs = {}, lemma = prop)
        # its interpolant may be too small

        while True:
            self.sanity_check_frame_monotone()
            self.sanity_check_imply()
            self.dump_frames()
            print ('Total Frames: %d, L %d , C %d ' %( len(self.frames) , len(self.frames[-1]), len(self.cexs_blocked.get(len(self.frames)-1,[]))))
            pause ()

            # frame[-1] /\ T -> not (prop)
            cube = self.get_bad_state_from_property_invalid_after_trans( \
                prop = prop, idx = len(self.frames)-1, use_init = False, remove_vars = remove_vars, keep_vars = keep_vars)

            print ('[Checking property] Get cube: ', cube , ' @F%d' % (len(self.frames)-1))
            # cube is list of (var, assignments)
            if cube is not None:
                # Blocking phase of a bad state
                if not self.recursive_block(cube, len(self.frames)-1, cex_origin = (None,'prop'), remove_vars, keep_vars ):
                    print("[Checking property] Bug found at step %d" % (len(self.frames)))
                    return False
                else:
                    print("[Checking property] Cube blocked '%s'" % self.print_cube(cube))
            else:
                # Checking if the last two frames are equivalent i.e., are inductive
                if self.is_last_two_frames_inductive():
                    print("[Checking property] The system is safe, frame : %d" % len(self.frames) )
                    return True
                else:
                    print("[Checking property] Adding frame %d..." % (len(self.frames)))
                    self.frames.append([])
                    self.push_lemma_from_the_lowest_frame(remove_vars, keep_vars) # TODO
                    if self.is_last_two_frames_inductive():
                        print("[Checking property] The system is safe, frame : %d" % len(self.frames) )
                        return True

                    # you should try to push existing clauses
    
    # TODO: problem : INIT -> next frame ????
    # put too few in the      
    def push_lemma_from_the_lowest_frame(self, remove_vars, keep_vars):
        start_frame = 1 # let's try not to worry about caching this at this time
        # do not push from the initial frame
        print ('[pushes] F%d --- F%d' % (start_frame, len(self.frames)-2))
        for fidx in range(start_frame, len(self.frames)-1):
            self.push_lemma_from_frame(fidx, remove_vars, keep_vars)

    # used in push lemma
    # it is okay not to add prop on the previous frame, already in the frame
    # it is okay not to deal with init
    def get_pre_post_state_from_property_invalid_after_trans(self, prop, fidx, T, variables, remove_vars, keep_vars ):
        prevF = self.frames[fidx]
        print ('      [pre_post_p_trans] Property:', prop.serialize())
        print ('      [pre_post_p_trans] var will => prime')
        #print ('      [pre_post_p_trans] prevF:', prevF)

        pre_ex = []
        post_ex = []

        if self.solver.solve( prevF + [T, Not( prop.substitute(self.prime_map))] ):
            model = self.solver.get_model()
            for v, val in model:
                if v in variables: # pre_ex
                    if v in remove_vars:
                        continue
                    if isinstance(keep_vars, list) and len(keep_vars) > 0 and v not in keep_vars:
                        continue
                    pre_ex.append((v,val))
                else:
                    v_primal = self.primal_map[v]
                    if v_primal in remove_vars:
                        continue
                    if isinstance(keep_vars, list) and len(keep_vars) > 0 and v_primal not in keep_vars:
                        continue
                    post_ex.append((v_primal,val))
            assert (len(pre_ex) > 0 and len(post_ex) > 0)
            return pre_ex, post_ex
                #
        return None, None # pre/post ex: None

    def shrink_var_cexs(self, cexs, fidx, varset, remove_vars, keep_vars):

        print ('  [shrink_var_cexs on F%d] get %d before shrink' % (fidx,len(cexs)))
        small_cexs = []
        set_idx_of_cex_blocked = set()

        for cidx, cube in enumerate(cexs):
            if _get_var(cube).issubset(varset):
                small_cexs.append(dict(cube))

            small_cube = []
            for v, val in cube:
                if v in varset:
                    small_cube.append((v, val))
            assert (len(small_cube) > 0)

            cex_origin = self.cex_origin.get(fidx,dict()).get(cidx,None)
            if self.recursive_block(small_cube, fidx, cex_origin = cex_origin, remove_vars = remove_vars, keep_vars = keep_vars):
                small_cexs.append(dict(small_cube))
                set_idx_of_cex_blocked.add(cidx)

                if (self.cexs_blocked[fidx][-1] == small_cube):
                    #self.dump_frames()
                    #print ('fidx:',fidx, '| cexs:', cexs, '| varset:', varset)
                    #print ('small_cube: ', str(small_cube))
                    set_idx_of_cex_blocked.add(len(self.cexs_blocked[fidx]) - 1) # subsume

        print ('  [shrink_var_cexs on F%d] get %d/%d after shrink' % (fidx,len(small_cexs), len(cexs)))
        return small_cexs, set_idx_of_cex_blocked

    # only used in push cex
    # in the case of cex pushed but not added to the next frame : it is subsumed!
    def get_cex_idx(self, cex, fidx):
        if cex not in self.cexs_blocked[fidx]:
            return '*subsume*'
        return (self.cexs_blocked[fidx].index(cex))


    def push_lemma_from_frame(self, fidx, remove_vars, keep_vars):
        def _add_lemma_and_cex_to_next_frame(lemma, lemmaIdx, cur_fidx):
            """have a lemma in the next frame and get its cex related stuff right"""
            fidx = cur_fidx
            if lemma not in self.frames[fidx+1]:
                # get the cidxs in the next frame
                # find the push cex list
                blocked_cexIdx_in_current_frame = self.lemma_to_cex_map_perframe.get(fidx, dict()).get(lemmaIdx, set())
                blocked_cexIdx_in_next_frame = set()
                for cidx in blocked_cexIdx_in_current_frame:
                    # push the cex 
                    cex = self.cexs_blocked[fidx][cidx]
                    origin = self.cex_origin[fidx][cidx]
                    # we don't check subsumption here
                    cexIdxFNext = self._add_cex(cex = cex, fidx = fidx + 1, origin = origin)
                    blocked_cexIdx_in_next_frame.add(blocked_cexIdx_in_next_frame)
                    # get cex status
                    assert self.cex_pushed_status[fidx][cidx] is not None
                    # with None, we previously already determined
                    # it is not possible to push, so this can not be true
                    if cidx is not in self.cex_pushed_status[fidx]:
                      self.cex_pushed_status[fidx][cidx] = cexIdxFNext # maybe there are overlapped cases

                # deal with lemma cex-idx map in the next frame (should be in the add_lemma part?)
                self._add_lemma(lemma = lemma, fidx = fidx + 1, cidxs = blocked_cexIdx_in_next_frame)
                # update statistics of cex--lemma
                for cidx in blocked_cexIdx_in_current_frame:
                    hashkey = self._canonicalize_cex( self.cexs_blocked[fidx][cidx] )
                    n_fail, n_total = self.cex_to_itp_push_fail.get(hashkey, (0,0))
                    self.cex_to_itp_push_fail[hashkey] = (n_fail, n_total+1)
            # deal with cex_covered_by_pushed_lemmas
            if fidx not in self.cex_covered_by_pushed_lemmas:
                self.cex_covered_by_pushed_lemmas[fidx] = set()
            # covered_cex =union= the cex idxs that it covered on this frame
            self.cex_covered_by_pushed_lemmas[fidx] = self.cex_covered_by_pushed_lemmas[fidx].union(\
                self.lemma_to_cex_map_perframe.get(fidx, dict()).get(lemmaIdx, set()) )
            # *** END OF _add_lemma_and_cex_to_next_frame ***


        #... think about push facts ???  always pushable!!! don't need to check
        assert (len(self.frames) > fidx+1)

        assert (len(self.frames[fidx]) > 0 )

        start_lemma_idx = self.frames_pushed_idxs_map.get(fidx, 0)
        end_lemma_idx   = len(self.frames[fidx]) # we can decide if we want to update this
        # iterate over the lemmas and the cex they blocked, tried to push 

        if (len(self.cexs_blocked.get(fidx,[])) == 0): # else no cex to push
            print ('  [push_lemma from F%d] <WARN> no cex to push from F%d'%(fidx,fidx))
            pause ()
            assert (False) # we should not expect this case
        #assert (fidx in self.cexs_blocked)

        if fidx in self.unblockable_fact:
            start_fact_idx = self.facts_pushed_idxs_map.get(fidx, 0)
            end_fact_idx = len(self.unblockable_fact[fidx])
            for factIdx in range(start_fact_idx, end_fact_idx):
                fact = self.unblockable_fact[fidx][factIdx]
                # once a fact always a fact
                if fact not in self.unblockable_fact.get(fidx+1,[]):
                    self._add_fact(fact = fact, fidx = fidx + 1)

        # IMPROVEMENT: cex and lemma push together ?
        # different cases:
        # 1. itself is pushable (GOOD)
        # push all pushable and then deal with unpushable, one by one

        # 2. itself is not pushable
        #     a. Does not block any, give it up
        #     b. cex is subsumed in the next (don't need this lemma actually)
        #     c. its cex is pushable (ITP --- different form, last resort)
        #     d. strengthen it with blocking its CTI (true CTI, too long, pushable)
        #        d1. try pushing all of --- 
        #        d2. 
        #     
        # finally check if any cex is not covered

        unpushed_lemmas = [] # list of (lidx, lemma, prev_ex, post_ex )

        if fidx not in self.cex_pushed_status:
            self.cex_pushed_status[fidx] = dict()

        for lemmaIdx in range(start_lemma_idx, end_lemma_idx):
            lemma = self.frames[fidx][lemmaIdx]
            print ('  [push_lemma F%d] Try pushing lemma l%d to F%d: ' % (fidx, lemmaIdx, fidx+1) , (lemma.serialize()))

            prev_ex, post_ex = \
                self.get_pre_post_state_from_property_invalid_after_trans(prop = lemma, fidx = fidx, \
                T = self.system.trans, variables = self.system.variables, \
                remove_vars = remove_vars, keep_vars = keep_vars )
            # variables there is to distinguish vars and prime vars

            if prev_ex is None: # post_ex should be none also
                # push is successful
                assert (post_ex is None)
                print ('  [push_lemma F%d] Succeed in pushing l%d!'%(fidx, lemmaIdx))
                _add_lemma_and_cex_to_next_frame(lemma = lemma, lemmaIdx = lemmaIdx, cur_fidx = fidx)
            else: # there is a failing model
                # store if temporarily and we will decide how to deal with them
                unpushed_lemmas.append((lemmaIdx, lemma, prev_ex, post_ex))
        # finish pushing all that can be pushed  
        # start to deal with unpushed

        move_lemma_list = [] # the (begin and end idxs for the lemma to be moved to the front?)
        for lemmaIdx, lemma, prev_ex, post_ex in unpushed_lemmas:
            # check if we really want to push this
            # if it has been covered by pushed lemmas, then we should be fine

            cexIdxs = self.lemma_to_cex_map_perframe.get(fidx, dict()).get(lemmaIdx, set())
            # cexIdxs is just the_cexIdxs_it_blocks
            if len(cexIdxs) == 0:
                print ('  [push_lemma F%d] will give up on lemma as it blocks None, '%(fidx), 'l'+str(lemmaIdx)+':',  lemma.serialize())
                continue
            # let's try its cex

            cannot_push = False, all_subsume = True, not_block_a_prop_cex = True
            list_of_cex_and_itp_from_cex = []
            assert (len(cexIdxs) == 1) , "NOT IMPLEMEMENTED!"
            for cexIdx in cexIdxs:
                if self.cex_origin[fidx][cexIdx][1] == 'prop':
                    not_block_a_prop_cex = False

                if cexIdx in self.cex_pushed_status[fidx] and self.cex_pushed_status[fidx][cexIdx] is None:
                    cannot_push = True
                    all_subsume = False
                    break

                # if it is not none:
                # we still want to know the itp

                cex_prop = _cube2prop(self.cexs_blocked[cexIdx])
                if self.is_valid( Implies(And(self.Frames[fidx+1]), cex_prop)) :  # Fidx+1 -> not _cex
                    continue # subsumed
                all_subsume = False
                ??? recursive_block try it here!!!
                model, itp = self.solveTrans(self.frames[fidx] , T = self.system.trans, prop = cex_prop, \
                    variables = self.system.variables, init = None, \
                    remove_vars = remove_vars, keep_vars = keep_vars, findItp = True )
                if model is not None:
                    self.cex_pushed_status[fidx][cexIdx] = None
                    cannot_push = True
                    all_subsume = False
                    break
                else: # use the itp
                    list_of_cex_and_itp_from_cex.append((cexIdx,itp))
                    # this is the last resort we shall use
                    # but still we can try which to use itp, which to ...

            # finish iterating cexs
            if cannot_push: # cannot push
                print ('  [push_lemma F%d] skip r-block l%d :'%(fidx, lemmaIdx) , lemma.serialize(), ' as its cex cannot be pushed.')
                # no itp to use actually
                continue

            if all_subsume: # no need to push
                print ('  [push_lemma F%d] skip r-block l%d :'%(fidx, lemmaIdx) , lemma.serialize(), ' as its cex has been subsumed.')
                continue

            if not not_block_a_prop_cex:
                print ('  [push_lemma F%d] start SyGuS repair l%d :'%(fidx, lemmaIdx) , lemma.serialize())

                SyGuS_repair_failed = True # by default, we will assume it is failed
                #################### SYGUS REPAIR ####################
                # update statistics of cex--lemma relation
                # after all previous update
                skip_this_lemma = False
                for cidx in cexIdxs:
                    hashkey = self._canonicalize_cex( self.cexs_blocked[fidx][cidx] )
                    n_fail, n_total = self.cex_to_itp_push_fail.get(hashkey, (0,0))
                    if n_fail+1 > Config_cex_invalid_itp_guess_threshold[0] * (n_total +1)/Config_cex_invalid_itp_guess_threshold[1] and n_total +1 > Config_cex_invalid_itp_guess_threshold[1]:
                        skip_this_lemma = True
                        break
                    self.cex_to_itp_push_fail[hashkey] = (n_fail+1, n_total+1) # once reach the limit we will not update it
                    n_fail, n_total = self.cex_to_itp_enhance_fail.get(hashkey, (0,0))
                    if n_fail > Config_enhance_giveup_threshold[0]*n_total/Config_enhance_giveup_threshold[1] and n_total > Config_enhance_giveup_threshold[1]:
                        skip_this_lemma = True
                        break
                # end of for all cex it blocks
                if skip_this_lemma:
                    print ('  [push_lemma F%d] skip SyGuS repair l%d :'%(fidx, lemmaIdx) , lemma.serialize(), ' too many failed itp/repair, skip')
                    ??? push its itp ???
                else: # let's truly start
                    # IMPROVEMENT: variable set change below
                    opextract = OpExtractor() # work on itp 
                    opextract.walk(lemma)
                    for _, new_itp in list_of_cex_and_itp_from_cex: # (cexidx , lemma)
                        opextract.walk(new_itp)
                    lemma_var_set = opextract.Symbols
                    post_ex_var_set = _get_var(post_ex) # this is necessary                
                    inv_var_set = lemma_var_set.union(post_ex_var_set)
                    sorted_inv_var_set = sorted(list(inv_var_set), key = lambda x: x.symbol_name())

                    blocked_cexs = [self.cexs_blocked[fidx][cidx] for cidx in cexIdxs] # fidx+1 is fewer cex

                    # it is a question on whether using fact actually ....
                    facts = self.unblockable_fact[fidx+1]         # facts should be more facts
                    facts_on_inv_vars = _get_cubes_with_more_var(facts, inv_var_set) # and will shrink var
                    sorted_allvars = sorted(self.system.variables, key = lambda x: x.symbol_name())
                    sorted_prime_vars = sorted(self.system.prime_variables, key = lambda x: x.symbol_name())

                    self.dump_frames()
                    print ('  [push_lemma F%d] Invoke SyGuS Now:'%(fidx))
                    print ('----------------\nvarset:\n',inv_var_set)
                    print ('----------------\ncex:\n',   blocked_cexs)
                    print ('----------------\nfacts:\n', facts_on_inv_vars)
                    if (len(cexs_on_inv_vars) == 0 or len(facts_on_inv_vars) == 0):
                        print ('  [push_lemma F%d] WARNING: no cex! skip sygus'%(fidx))
                        input ()
                        continue

                    # this is very important ? to remove the old one ? so it is a replacement
                    cex_guided_pbe = CexGuidedPBE( \
                        primal_vars = self.system.variables,
                        prime_vars  = self.system.prime_variables,
                        primal_map  = self.primal_map, # next_v --> v
                        prime_map   = self.prime_map, # v --> next_v
                        T =  self.system.trans,
                        F_idx_minus2 = [self.frames[fidx][lidx] for lidx in range(len(self.frames[fidx])) if lidx != lemmaIdx],
                        Init = self.system.init, # IMPROVEMENT: Use init
                        inv_var_set = inv_var_set, # we can change this if necessary
                        facts_on_inv_vars = facts_on_inv_vars if Config_use_fact_in_sygus else [],
                        cexs_on_inv_vars = blocked_cexs,
                        sorted_inv_var_set = sorted_inv_var_set,
                        sorted_allvars = sorted_allvars,
                        sorted_prime_vars = sorted_prime_vars,
                        op_obj = opextract)

                    # lemma /\ F /\ T => lemma'
                    itp = cex_guided_pbe.syn_lemma_F_T_implies_lemma_prime( \
                        fidx = fidx, lidx = lemmaIdx, itp = lemma, \
                        frame_dump = self.dump_frames(toStr = True))

                    if itp is None:
                        print ('  [push_lemma F%d] Repair lemma l%d failed: ' % (fidx, lemmaIdx))
                        if len(cexIdxs) == 1:
                            for cidx in cexIdxs:
                                hashkey = self._canonicalize_cex( self.cexs_blocked[fidx][cidx] )
                                n_fail, n_total = self.cex_to_itp_enhance_fail.get(hashkey, (0,0))
                                self.cex_to_itp_enhance_fail[hashkey] = (n_fail+1, n_total+1)
                    else: # we have a good itp !!!
                        SyGuS_repair_failed = False # this will stop current iteration
                        itp_prime_var = itp.substitute(cex_guided_pbe.prime_map)
                        #md = self.solve(Not(Implies(And(self.frames[fidx] + [self.system.trans, itp]), itp_prime_var ) ) )
                        #if md is not None:
                        #    print (md)
                        # assert (init -> lemma)
                        assert (self.is_valid(Implies(self.system.init, itp)))
                        # assert (lemma /\ F /\ T => lemma')
                        # compared to the syn constraint, this is actually stronger
                        assert (self.is_valid(Implies(And(self.frames[fidx] + [self.system.trans, itp]), itp_prime_var ) ) )
                        # if not (F[fidx-1]) => itp
                        #   add to all previous frames
                        # now we add cex to the next frame
                        _add_lemma_and_cex_to_next_frame(lemma = itp, lemmaIdx = lemmaIdx, cur_fidx = fidx)
                        #if (self.solve(Not(Implies(And(self.frames[fidx-1]), itp))) is not None):
                        print ('  [push_lemma F%d] Add to all prev frame '%(fidx) )
                        self.frames[fidx][lemmaIdx] = And(lemma, itp)
                        # we don't want to touch the lemma Idx which will mess things up
                        self._add_lemma_to_all_prev_frame(end_frame_id = fidx-1, lemma = itp)
                        # end of the for loop for repairing lemmas
                    # *** END OF itp is not None ***
                # ** END of not skip SyGuS ***
                if not SyGuS_repair_failed:
                    continue # we successfully repair this lemma

                #################### CONTRACTION REPAIR ####################
                # 
                print ('  [push_lemma F%d] start strengthen l%d :'%(fidx, lemmaIdx) , lemma.serialize())
                # high priority push this one
                frame_cached_idx = len(self.frames[fidx])
                cex_cached_idx = len(self.cexs_blocked[fidx])
                strength_prop_succeeded = False
                strengthen_time_out = False
                strengthen_time = 0
                # will try at most this times, should be a while loop here, but you cannot prune infinite many times
                while True:
                  strengthen_time += 1
                  if self.recursive_block(prev_ex, fidx, cex_origin = (None,'push_lemma'), remove_vars, keep_vars ):
                      if strengthen_time > Config_strengthen_effort_for_prop:
                          print ('  [push_lemma F%d] strengthen time out:'%(fidx))
                          strengthen_time_out = True
                          break
                      print ('  [push_lemma F%d] cex blocked:'%(fidx) , "will retry push lemma")
                      prev_ex, post_ex = \
                          self.get_pre_post_state_from_property_invalid_after_trans(prop = lemma, fidx = fidx, \
                          T = self.system.trans, variables = self.system.variables, \
                          remove_vars = remove_vars, keep_vars = keep_vars )
                      if prev_ex is None:
                          strength_prop_succeeded = True
                          break
                  else: # cannot block 
                      break

                if strength_prop_succeeded:
                    # see if we can push its support all to the next level
                    # if not we will leave them there 
                    # and only push one thing
                    assert (len(self.frames[fidx]) - frame_cached_idx == len(self.blocked_cexs[fidx]) - cex_cached_idx)
                    conj_prop = And(lemma, self.frames[fidx][frame_cached_idx:])

                    prev_ex, post_ex = \
                        self.get_pre_post_state_from_property_invalid_after_trans(prop = conj_prop, fidx = fidx, \
                        T = self.system.trans, variables = self.system.variables, \
                        remove_vars = remove_vars, keep_vars = keep_vars )
                    if prev_ex is None:
                        # okay to push combination of them
                        _add_lemma_and_cex_to_next_frame(lemma = lemma, lemmaIdx = lemmaIdx, cur_fidx = fidx)
                        # will move later
                        move_lemma_list.append((frame_cached_idx, len(self.frames[fidx])))
                        for new_lidx in range(frame_cached_idx, len(self.frames[fidx])):
                            _add_lemma_and_cex_to_next_frame(lemma = self.frames[fidx][new_lidx], \
                                lemmaIdx = lemmaIdx, cur_fidx = fidx)
                        # now we should move them to already pushed ones
                    else:
                        _add_lemma_and_cex_to_next_frame(lemma = lemma, lemmaIdx = lemmaIdx, cur_fidx = fidx)
                    continue # end with success
                else:
                    if strengthen_time_out:
                      # we know for sure it can be blocked
                      # do we want to repair an individual one ? maybe do it elsewhere
                      pass
                    else: # true fact
                      self._add_fact(fact = prev_ex, fidx = fidx)
            # *** END OF prop lemma repair ***
            else:
                print ('  [push_lemma F%d] skip sygus/contract repair l%d :'%(fidx, lemmaIdx) , lemma.serialize(), ' as it does not block prop cex')
                pass

            #################### ITP CHANGE FORM ####################
            for cexIdx, _ in list_of_cex_and_itp_from_cex:
                cex_origin = self.cex_origin[fidx][cexIdx] # push should remain the same create origin!!!
                cex = self.cexs_blocked[fidx][cexIdx]
                print ('  [push_lemma F%d] cex to try: c%d :'%(fidx, cexIdx), self.print_cube(cex))


                assert self.recursive_block(cex, fidx+1, cex_origin = (cexIdx, cex_origin[1]), remove_vars, keep_vars ):
                #  cex_origin[1] is cex_create_origin
                print ('  [push_lemma F%d] cex is pushed: '%fidx, self.print_cube(cex))
                self.cex_pushed_status[fidx].append( self.get_cex_idx(cex,fidx+1) ) # the text value is not used at all

            # idx adjustment
            move_lemma_list
            # idx updates

            #cannot block

            



            >> TODO # when later we finally pushed, do push the cexes !!!


                # see if cannnot be pushed
                # and collect ITPs

            # 1. try syn without facts
            # 2. try strengthen, but push the group
            #      may leave (push lemma) lemma in prior frames: we don't care
            #      need to have a depth
            #      try re-syn those not pushable (block the same cex, and in the next frame)



    def is_last_two_frames_inductive(self):
        """Checks if last two frames are equivalent (no need to change variable to prime)"""
        if len(self.frames) > 1 and \
             self.is_valid((Implies(And(self.frames[-1]), And(self.frames[-2]) ))):
                return True
        return False

    # used in check_property, check_init_failed
    # not in push_lemma, because we also want the pre-&post-states
    def get_bad_state_from_property_invalid_after_trans(self, prop, idx, use_init, remove_vars = [], keep_vars = None):
        """Extracts a reachable state that intersects the negation
        of the property and the last current frame"""
        assert (idx >= 0)
        print ('    [F%d -> prop]' % idx)
        md, itp = self.solveTrans(self.frames[idx], \
            T = self.system.trans, prop = prop, \
            init = self.system.init if use_init else None,
            variables = self.system.variables, \
            remove_vars = remove_vars, keep_vars = keep_vars, findItp = True )
        # no need for itp here
        #pause()
        return md

    def is_valid(self, prop):
        if self.valid_solver.solve(Not(prop)):
            return False
        return True

    def get_not_valid_model(self, prop):
        if self.valid_solver.solve(Not(prop)):
            return self.valid_solver.get_model()
        return None

    def solve(self, formula, remove_vars = [], keep_vars = None):
        """Provides a satisfiable assignment to the state variables that are consistent with the input formula"""
        # you should know to drop variables here
        # plus tenary simulation ? ast-walker
        if not isinstance(formula, list):
            formula = [formula]
        if self.solver.solve(formula):
            retL = []
            for v, val in self.solver.get_model():
                if v in remove_vars:
                    continue
                if (isinstance(keep_vars, list) or isinstance(keep_vars, set) ) and len(keep_vars) > 0 and v not in keep_vars:
                    continue
                retL.append((v,val))
                #retL.append(EqualsOrIff(v, val))
            assert (len(retL) > 0) # otherwise we are removing too many variables!
            #return And(retL)
            return retL
        return None


    # you may want to have the interpolant here
    # used in recursive_block  and  get_bad_state_from_property_invalid_after_trans
    def solveTrans(self, prevF, T, prop , variables, init, remove_vars = [], keep_vars = None, findItp = False):
        # prevF /\ T(p, prime) --> not prop, if sat
        print ('      [solveTrans] Property:', prop.serialize())
        print ('      [solveTrans] var will => prime')
        #print ('      [solveTrans] prevF:', prevF)
        print ('      [solveTrans] use Init:', init is not None)

        if init is None:
            f = prevF + [T, Not( prop.substitute(self.prime_map))]
        else:
            f = [Or(And(prevF+[T]), init.substitute(self.prime_map) ) , Not( prop.substitute(self.prime_map))]
        #print (f)

        if self.solver.solve(f):
            model = self.solver.get_model()
            retL = []
            for v, val in model:
                if v not in variables: # if it is prime variable
                    continue # ignore it
                if v in remove_vars:
                    continue
                if isinstance(keep_vars, list) and len(keep_vars) > 0 and v not in keep_vars:
                    continue
                retL.append((v,val))
            assert (len(retL) > 0) # otherwise we are removing too many variables!
            #return And(retL)
            return retL, None
        Itp = None
        if findItp:
            if init is None:
                a = And(prevF + [T])
                b = Not( prop.substitute(self.prime_map))
            else:
                a = f[0]
                b = f[1]
            Itp = self.itp_solver.binary_interpolant( a = a, b = b)
            Itp = And(Itp)
            Itp = Itp.substitute(self.primal_map)
            if Config_simplify_itp:
                Itp = simplify(Itp)
            print ('    [solveTrans] get itp: ', Itp.serialize())
            #pause()
        return None, Itp



    # ---------------------------------------------------------------------------------
    def get_inv(self):
        return And(self.frames[-1])

    def sanity_check_inductive_inv(self, prop ):
        T = self.system.trans
        inv = self.get_inv()
        inv_prime = inv.substitute(self.prime_map)
        assert ( self.is_valid(Implies(self.system.init,inv)))
        assert ( self.is_valid(Implies(And(inv, T), inv_prime)))
        assert ( self.is_valid(Implies(inv, prop)))

    def sanity_check_imply(self):
        assert (len(self.frames) > 1)
        T = self.system.trans
        for fidx in range(1,len(self.frames)):
            next_frame = And(self.frames[fidx])
            next_frame = next_frame.substitute(self.prime_map)
            assert ( self.is_valid(Implies(And(self.frames[fidx-1] + [T]), next_frame)) )
            #if model is not None:
            #    print ('Bug, F%d and T -/-> F%d' % (fidx-1, fidx))
            #    assert (False)

    def sanity_check_frame_monotone(self):
        assert (len(self.frames) > 1)
        for fidx in range(1,len(self.frames)):
            valid = self.is_valid(Implies(And(self.frames[fidx-1]), And(self.frames[fidx])))
            if not valid:
                self.dump_frames()
                print ('Bug, not monotone, F%d -> F%d' % (fidx-1, fidx))

                print ('Bug lemmas in F%d' % fidx)
                for lemmaIdx, lemma in enumerate(self.frames[fidx]):
                    model = self.get_not_valid_model(Implies(And(self.frames[fidx-1]), lemma))
                    if model is not None:
                        print (' l%d : ' % lemmaIdx, lemma.serialize())
                assert (False)

    @staticmethod
    def print_cube(c):
        return ( '(' + ( ' && '.join([v.symbol_name() + ' = ' + str(val) for v, val in c]) ) + ')'  ) 


    # ---------------------------------------------------------------------------------
                
    def recursive_block(self, cube, idx, cex_origin, remove_vars = [], keep_vars = None ):
        assert isinstance(cex_origin, tuple )
        cex_push_origin = cex_origin[0]
        cex_create_origin = cex_origin[1]

        priorityQueue = []
        print ('      [block] Try @F%d' % idx, self.print_cube(cube) )

        prop = _cube2prop(cube)
        if self.solve(self.frames[idx] + [Not( prop )] ) is None:
            print ('      [block] already blocked by F%d' % idx)
            return True

        heapq.heappush(priorityQueue, (idx, cube))
        while len(priorityQueue) > 0:
            fidx, cex = heapq.nsmallest(1, priorityQueue)[0]

            if fidx == 0:
                model_init_frame = self.solve( \
                    [self.system.init] +  [EqualsOrIff(v,val) for v,val in cex])
                assert (model_init_frame is not None)
                print ('      [block] CEX found!')
                return False

            prop = Not(And([EqualsOrIff(v,val) for v,val in cex]))
            
            # Question: too old itp? useful or not?
            # push on older frames also? for new ITP?
            print ('      [block] check at F%d -> F%d : ' % (fidx-1, fidx), str(prop)  )
            #if Config_rm_cex_in_prev:
            #    if (self.solve( \
            #            [self.system.init] +  [EqualsOrIff(v,val) for v,val in cex]) is not None):
            #        print ('      [block] CEX is reachable -- direct init!')
            #        return False
            
            model, itp = self.solveTrans(self.frames[fidx-1] + ([prop] if Config_rm_cex_in_prev else []), \
                T = self.system.trans, prop = prop, \
                variables = self.system.variables, \
                init = self.system.init, \
                remove_vars = remove_vars, keep_vars = keep_vars, findItp = True )

            if model is None:
                if cex_push_origin is not None:
                  new_cex_push_origin = cex_push_origin if idx == fidx else None
                else:
                  new_cex_push_origin = None

                cidx = self._add_cex(fidx = fidx, cex = cex, origin = (new_cex_push_origin, cex_create_origin))

                self._add_lemma(lemma = itp, fidx = fidx, cidxs = {cidx} )
                if not self.is_valid( Implies(And(self.frames[fidx-1]), itp) ):
                    self._add_lemma_to_all_prev_frame( end_frame_id = fidx-1, lemma = itp )
                    print ('    [block] add ITP to F1 ->>- F%d: ' % (fidx-1), itp.serialize())
                    # add cex to all previous ones and this will block it 
                    # or, maybe you don't need it because it is already pushed before the current frame
                    # and should not interfere with the not yet pushed lemma.

                heapq.heappop(priorityQueue) # pop this cex

            else:
                # model is not None
                print ('      [block] push to queue, F%d' % (fidx-1), self.print_cube(model))
                heapq.heappush(priorityQueue, (fidx-1, model))
        # TODO: 
        print ('      [block] Succeed, return.')
        return True

        # for the CTG, see if we can block it or not?


def test_naive_pdr():
    width = 16
    cnt = BaseAddrCnt(width)
    prop = cnt.neq_property(1 << (width-1),1,1)
    pdr = PDR(cnt)
    pdr.check_property(prop)
    pdr.sanity_check_imply()
    pdr.sanity_check_frame_monotone()
    pdr.sanity_check_inductive_inv(prop)
    pdr.dump_frames()
    print ('inv: ', simplify(pdr.get_inv()).serialize())



def test_naive_pdr_2cnt():
    width = 16
    cnt = TwoCnt(width, zero_init = True)
    #prop_good = cnt.false_property(65536-1001,1000)
    prop = cnt.neq_property(65536-1000,1000)
    pdr = PDR(cnt)
    pdr.check_property(prop)
    pdr.sanity_check_imply()
    pdr.sanity_check_frame_monotone()
    pdr.sanity_check_inductive_inv(prop)
    pdr.dump_frames()
    print ('inv: ', simplify(pdr.get_inv()).serialize())


def test_naive_pdr_2cnt_noload():
    width = 16
    cnt = TwoCntNoload(width, zero_init = True)
    #prop_good = cnt.false_property(65536-1001,1000)
    prop = cnt.neq_property(65536-1000,1000)
    pdr = PDR(cnt)
    pdr.check_property(prop)
    pdr.sanity_check_imply()
    pdr.sanity_check_frame_monotone()
    pdr.sanity_check_inductive_inv(prop)
    pdr.dump_frames()
    print ('inv: ', simplify(pdr.get_inv()).serialize())


if __name__ == '__main__':
    test_naive_pdr()
