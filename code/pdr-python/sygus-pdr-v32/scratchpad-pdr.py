
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


    # TODO: problem : INIT -> next frame ????
    # put too few in the      
    def push_lemma_from_the_lowest_frame(self, remove_vars, keep_vars):
        start_frame = 1 # let's try not to worry about caching this at this time
        # do not push from the initial frame
        print ('[pushes] F%d --- F%d' % (start_frame, len(self.frames)-2))
        for fidx in range(start_frame, len(self.frames)-1):
            self.push_lemma_from_frame(fidx, remove_vars, keep_vars)

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




    # ---------------------------------------------------------------------------------


    # ---------------------------------------------------------------------------------
             


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
