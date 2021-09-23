


















            # update statistics of cex--lemma relation
            # after all previous update
            if len(cexIdxs) == 1:
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

                if skip_this_lemma:
                    print ('  [push_lemma F%d] skip l%d :'%(fidx, lemmaIdx) , lemma.serialize(), ' too many failed itp/repair, skip')
                    continue

            print ('  [push_lemma F%d] start repair l%d :'%(fidx, lemmaIdx) , lemma.serialize())


                if len(the_cexIdxs_it_blocks) == 0:
                    print ('  [push_lemma F%d] will give up on lemma as it blocks None, '%(fidx), 'l'+str(lemmaIdx)+':',  lemma.serialize())
                    break


                # if forall c: it blocks, c is subsumed or pushed by others, will not try to carve out the
                # current space

                # if exist c: it blocks, that cannot be push, no sense to try to cut the current space

                # if it blocks no prop cex, no need to try to cut space ?? IMPROVEMENT : design choice & experiment
                status_list=self.cex_pushed_status.get(fidx,dict())
                allSubsumed = True, failedBlockedCex = False, block_a_prop_cex = False

                for cidx in the_cexIdxs_it_blocks:
                    if cidx < len(status_list):
                        if status_list[cidx] != '*subsume*':
                            allSubsumed = False
                        if status_list[cidx] is None:
                            failedBlockedCex = True
                        # check the origin, if origins has no prop, will not try hard
                        create_origin = self.cex_origin[fidx][cidx][1]
                        if create_origin == 'prop':
                            block_a_prop_cex = True

                if failedBlockedCex: # skip recursive-block
                    print ('  [push_lemma F%d] skip r-block l%d :'%(fidx, lemmaIdx) , lemma.serialize(), ' as its cex cannot be pushed.')
                    break

                if allSubsumed: # skip recursive-block
                    print ('  [push_lemma F%d] skip r-block l%d :'%(fidx, lemmaIdx) , lemma.serialize(), ' as its cex has been subsumed.')
                    break

                if the_cexIdxs_it_blocks.issubset( self.cex_covered_by_pushed_lemmas.get(fidx, set()) ):
                    print ('  [push_lemma F%d] skip r-block l%d :'%(fidx, lemmaIdx) , lemma.serialize(), ' as it has been covered by other successful pushes')
                    break

                if not block_a_prop_cex:
                    print ('  [push_lemma F%d] skip r-block l%d :'%(fidx, lemmaIdx) , lemma.serialize(), ' as it does not block prop cex')
                    break

                # prev_ex is not None
                # try recursive block
                if prev_ex not in self.unblockable_fact.get(fidx,[]):
                    if self.recursive_block(prev_ex, fidx, cex_origin = (None,'push_lemma'), remove_vars, keep_vars ):
                        print ('  [push_lemma F%d] cex blocked:'%(fidx) , "will retry push lemma")
                        continue # try in next round
                    # else recursive block failed
                    # put it in the fact
                    print ('  [push_lemma F%d] fail due to pre-fact :'%fidx , self.print_cube(prev_ex))
                    print ('  [push_lemma F%d] post-fact :'%fidx , self.print_cube(post_ex))
                    self._add_fact(fact=prev_ex, fidx=fidx) # add pre fact only if not in fact
                # always add post fact
                self._add_fact(fact=post_ex, fidx=fidx+1)

                unpushed_lemmas.append((lemmaIdx, lemma, prev_ex, post_ex))
                break 

            
        # ---------------------------------------------------------------------------------------------------------


        for lemmaIdx in range(start_lemma_idx, end_lemma_idx):
            lemma = self.frames[fidx][lemmaIdx]
            print ('  [push_lemma F%d] Try pushing lemma l%d to F%d: ' % (fidx, lemmaIdx, fidx+1) , (lemma.serialize()))

            
            while True: # try push

                prev_ex, post_ex = \
                    self.get_pre_post_state_from_property_invalid_after_trans(prop = lemma, fidx = fidx, \
                    T = self.system.trans, variables = self.system.variables, \
                    remove_vars = remove_vars, keep_vars = keep_vars )

                if prev_ex is None: # post_ex should be none also
                    assert (post_ex is None)
                    print ('  [push_lemma F%d] Succeed in pushing l%d!'%(fidx, lemmaIdx))
                    if Config_use_itp_in_pushing:
                        print ('  [push_lemma F%d] And we add its ITP!'%fidx) # do we really do this? not necessary I think
                    if lemma not in self.frames[fidx+1]:
                        # get the cidxs in the next frame
                        # find the push cex list
                        blocked_cexIdx_in_current_frame = self.lemma_to_cex_map_perframe.get(fidx, dict()).get(lemmaIdx, set())
                        blocked_cexIdx_in_next_frame = set()
                        for cidx in blocked_cexIdx_in_current_frame:
                            nxt_idx = self.cex_pushed_status.get(fidx,[])[cidx]
                            assert (nxt_idx is not None) 
                            if nxt_idx == '*subsume*':
                                continue # do not add subsumed cex
                            # it must have been pushed successfully, otherwise, how could the itp pushed succesfully
                            blocked_cexIdx_in_next_frame.add(nxt_idx)

                        # deal with lemma cex-idx map in the next frame (should be in the add_lemma part?)
                        self._add_lemma(lemma = lemma, fidx = fidx + 1, cidxs = blocked_cexIdx_in_next_frame)

                        # update statistics of cex--lemma
                        if len(blocked_cexIdx_in_current_frame) == 1:
                            for cidx in blocked_cexIdx_in_current_frame:
                                hashkey = self._canonicalize_cex( self.cexs_blocked[fidx][cidx] )
                                n_fail, n_total = self.cex_to_itp_push_fail.get(hashkey, (0,0))
                                self.cex_to_itp_push_fail[hashkey] = (n_fail, n_total+1)

                    # deal with cex_covered_by_pushed_lemmas
                    if fidx not in self.cex_covered_by_pushed_lemmas:
                        self.cex_covered_by_pushed_lemmas[fidx] = set()

                    # covered_cex =union= the cex idxs that it covered on this frame
                    self.cex_covered_by_pushed_lemmas[fidx] = self.cex_covered_by_pushed_lemmas[fidx].union(\
                        self.lemma_to_cex_map_perframe.get(fidx, dict()).get(lemmaIdx, set())  )

                    break

                print ('  [push_lemma F%d] Get pre cex:'%(fidx), prev_ex)
                the_cexIdxs_it_blocks = self.lemma_to_cex_map_perframe.get(fidx, dict()).get(lemmaIdx, set())
                if len(the_cexIdxs_it_blocks) == 0:
                    print ('  [push_lemma F%d] will give up on lemma as it blocks None, '%(fidx), 'l'+str(lemmaIdx)+':',  lemma.serialize())
                    break


                # if forall c: it blocks, c is subsumed or pushed by others, will not try to carve out the
                # current space

                # if exist c: it blocks, that cannot be push, no sense to try to cut the current space

                # if it blocks no prop cex, no need to try to cut space ?? IMPROVEMENT : design choice & experiment
                status_list=self.cex_pushed_status.get(fidx,[])
                allSubsumed = True, failedBlockedCex = False, block_a_prop_cex = False

                for cidx in the_cexIdxs_it_blocks:
                    if cidx < len(status_list):
                        if status_list[cidx] != '*subsume*':
                            allSubsumed = False
                        if status_list[cidx] is None:
                            failedBlockedCex = True
                        # check the origin, if origins has no prop, will not try hard
                        create_origin = self.cex_origin[fidx][cidx][1]
                        if create_origin == 'prop':
                            block_a_prop_cex = True

                if failedBlockedCex: # skip recursive-block
                    print ('  [push_lemma F%d] skip r-block l%d :'%(fidx, lemmaIdx) , lemma.serialize(), ' as its cex cannot be pushed.')
                    break

                if allSubsumed: # skip recursive-block
                    print ('  [push_lemma F%d] skip r-block l%d :'%(fidx, lemmaIdx) , lemma.serialize(), ' as its cex has been subsumed.')
                    break

                if the_cexIdxs_it_blocks.issubset( self.cex_covered_by_pushed_lemmas.get(fidx, set()) ):
                    print ('  [push_lemma F%d] skip r-block l%d :'%(fidx, lemmaIdx) , lemma.serialize(), ' as it has been covered by other successful pushes')
                    break

                if not block_a_prop_cex:
                    print ('  [push_lemma F%d] skip r-block l%d :'%(fidx, lemmaIdx) , lemma.serialize(), ' as it does not block prop cex')
                    break

                # prev_ex is not None
                # try recursive block
                if prev_ex not in self.unblockable_fact.get(fidx,[]):
                    if self.recursive_block(prev_ex, fidx, cex_origin = (None,'push_lemma'), remove_vars, keep_vars ):
                        print ('  [push_lemma F%d] cex blocked:'%(fidx) , "will retry push lemma")
                        continue # try in next round
                    # else recursive block failed
                    # put it in the fact
                    print ('  [push_lemma F%d] fail due to pre-fact :'%fidx , self.print_cube(prev_ex))
                    print ('  [push_lemma F%d] post-fact :'%fidx , self.print_cube(post_ex))
                    self._add_fact(fact=prev_ex, fidx=fidx) # add pre fact only if not in fact
                # always add post fact
                self._add_fact(fact=post_ex, fidx=fidx+1)

                unpushed_lemmas.append((lemmaIdx, lemma, prev_ex, post_ex))
                break 
            # now handle the unpushed altogether

        # -------------------------------------------------------------


        
        if fidx in self.cexs_blocked:

            start_cexs_idx = self.cexs_pushed_idxs_map.get(fidx,0)
            end_cex_idx    = len(self.cexs_blocked[fidx])

            if fidx not in self.cex_pushed_status:
                self.cex_pushed_status[fidx] = []
            assert (start_cexs_idx == len(self.cex_pushed_status[fidx]))  #make should the push status is synced

            for cexIdx in range(start_cexs_idx,end_cex_idx):
                cex_origin = self.cex_origin[fidx][cexIdx] # push should remain the same create origin!!!

                cex = self.cexs_blocked[fidx][cexIdx]
                print ('  [push_lemma F%d] cex to try: c%d :'%(fidx, cexIdx), self.print_cube(cex))
                if self.recursive_block(cex, fidx+1, cex_origin = (cexIdx, cex_origin[1]), remove_vars, keep_vars ):
                    #  cex_origin[1] is cex_create_origin
                    print ('  [push_lemma F%d] cex is pushed: '%fidx, self.print_cube(cex))
                    self.cex_pushed_status[fidx].append( self.get_cex_idx(cex,fidx+1) )
                else:
                    self.cex_pushed_status[fidx].append(None)

            self.cexs_pushed_idxs_map[fidx] =  end_cex_idx # we have push all the cexs at the early time
            # in the process of pushing we may block additional cexs

        # if len(self.cexs_blocked[fidx]) > end_cex_idx: there are now more cexs to try pushing
        # there could be more cexs to push (we can decide if we want to add a loop here)

        unpushed_lemmas = [] # list of (lidx, lemma, prev_ex, post_ex )

        for lemmaIdx in range(start_lemma_idx, end_lemma_idx):
            lemma = self.frames[fidx][lemmaIdx]
            print ('  [push_lemma F%d] Try pushing lemma l%d to F%d: ' % (fidx, lemmaIdx, fidx+1) , (lemma.serialize()))

            
            while True: # try push

                prev_ex, post_ex = \
                    self.get_pre_post_state_from_property_invalid_after_trans(prop = lemma, fidx = fidx, \
                    T = self.system.trans, variables = self.system.variables, \
                    remove_vars = remove_vars, keep_vars = keep_vars )

                if prev_ex is None: # post_ex should be none also
                    assert (post_ex is None)
                    print ('  [push_lemma F%d] Succeed in pushing l%d!'%(fidx, lemmaIdx))
                    if Config_use_itp_in_pushing:
                        print ('  [push_lemma F%d] And we add its ITP!'%fidx) # do we really do this? not necessary I think
                    if lemma not in self.frames[fidx+1]:
                        # get the cidxs in the next frame
                        # find the push cex list
                        blocked_cexIdx_in_current_frame = self.lemma_to_cex_map_perframe.get(fidx, dict()).get(lemmaIdx, set())
                        blocked_cexIdx_in_next_frame = set()
                        for cidx in blocked_cexIdx_in_current_frame:
                            nxt_idx = self.cex_pushed_status.get(fidx,[])[cidx]
                            assert (nxt_idx is not None) 
                            if nxt_idx == '*subsume*':
                                continue # do not add subsumed cex
                            # it must have been pushed successfully, otherwise, how could the itp pushed succesfully
                            blocked_cexIdx_in_next_frame.add(nxt_idx)

                        # deal with lemma cex-idx map in the next frame (should be in the add_lemma part?)
                        self._add_lemma(lemma = lemma, fidx = fidx + 1, cidxs = blocked_cexIdx_in_next_frame)

                        # update statistics of cex--lemma
                        if len(blocked_cexIdx_in_current_frame) == 1:
                            for cidx in blocked_cexIdx_in_current_frame:
                                hashkey = self._canonicalize_cex( self.cexs_blocked[fidx][cidx] )
                                n_fail, n_total = self.cex_to_itp_push_fail.get(hashkey, (0,0))
                                self.cex_to_itp_push_fail[hashkey] = (n_fail, n_total+1)

                    # deal with cex_covered_by_pushed_lemmas
                    if fidx not in self.cex_covered_by_pushed_lemmas:
                        self.cex_covered_by_pushed_lemmas[fidx] = set()

                    # covered_cex =union= the cex idxs that it covered on this frame
                    self.cex_covered_by_pushed_lemmas[fidx] = self.cex_covered_by_pushed_lemmas[fidx].union(\
                        self.lemma_to_cex_map_perframe.get(fidx, dict()).get(lemmaIdx, set())  )

                    break

                print ('  [push_lemma F%d] Get pre cex:'%(fidx), prev_ex)
                the_cexIdxs_it_blocks = self.lemma_to_cex_map_perframe.get(fidx, dict()).get(lemmaIdx, set())
                if len(the_cexIdxs_it_blocks) == 0:
                    print ('  [push_lemma F%d] will give up on lemma as it blocks None, '%(fidx), 'l'+str(lemmaIdx)+':',  lemma.serialize())
                    break


                # if forall c: it blocks, c is subsumed or pushed by others, will not try to carve out the
                # current space

                # if exist c: it blocks, that cannot be push, no sense to try to cut the current space

                # if it blocks no prop cex, no need to try to cut space ?? IMPROVEMENT : design choice & experiment
                status_list=self.cex_pushed_status.get(fidx,[])
                allSubsumed = True, failedBlockedCex = False, block_a_prop_cex = False

                for cidx in the_cexIdxs_it_blocks:
                    if cidx < len(status_list):
                        if status_list[cidx] != '*subsume*':
                            allSubsumed = False
                        if status_list[cidx] is None:
                            failedBlockedCex = True
                        # check the origin, if origins has no prop, will not try hard
                        create_origin = self.cex_origin[fidx][cidx][1]
                        if create_origin == 'prop':
                            block_a_prop_cex = True

                if failedBlockedCex: # skip recursive-block
                    print ('  [push_lemma F%d] skip r-block l%d :'%(fidx, lemmaIdx) , lemma.serialize(), ' as its cex cannot be pushed.')
                    break

                if allSubsumed: # skip recursive-block
                    print ('  [push_lemma F%d] skip r-block l%d :'%(fidx, lemmaIdx) , lemma.serialize(), ' as its cex has been subsumed.')
                    break

                if the_cexIdxs_it_blocks.issubset( self.cex_covered_by_pushed_lemmas.get(fidx, set()) ):
                    print ('  [push_lemma F%d] skip r-block l%d :'%(fidx, lemmaIdx) , lemma.serialize(), ' as it has been covered by other successful pushes')
                    break

                if not block_a_prop_cex:
                    print ('  [push_lemma F%d] skip r-block l%d :'%(fidx, lemmaIdx) , lemma.serialize(), ' as it does not block prop cex')
                    break

                # prev_ex is not None
                # try recursive block
                if prev_ex not in self.unblockable_fact.get(fidx,[]):
                    if self.recursive_block(prev_ex, fidx, cex_origin = (None,'push_lemma'), remove_vars, keep_vars ):
                        print ('  [push_lemma F%d] cex blocked:'%(fidx) , "will retry push lemma")
                        continue # try in next round
                    # else recursive block failed
                    # put it in the fact
                    print ('  [push_lemma F%d] fail due to pre-fact :'%fidx , self.print_cube(prev_ex))
                    print ('  [push_lemma F%d] post-fact :'%fidx , self.print_cube(post_ex))
                    self._add_fact(fact=prev_ex, fidx=fidx) # add pre fact only if not in fact
                # always add post fact
                self._add_fact(fact=post_ex, fidx=fidx+1)

                unpushed_lemmas.append((lemmaIdx, lemma, prev_ex, post_ex))
                break 
            # now handle the unpushed altogether

        for lemmaIdx, lemma, prev_ex, post_ex in unpushed_lemmas:
            # check if we really want to push this
            # if it has been covered by pushed lemmas, then we should be fine
            cexIdxs = self.lemma_to_cex_map_perframe.get(fidx, dict()).get(lemmaIdx, set())
            assert len(cexIdxs) > 0, "BUG: should already given up by first try"

            # update statistics of cex--lemma relation
            # after all previous update
            if len(cexIdxs) == 1:
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

                if skip_this_lemma:
                    print ('  [push_lemma F%d] skip l%d :'%(fidx, lemmaIdx) , lemma.serialize(), ' too many failed itp/repair, skip')
                    continue

            print ('  [push_lemma F%d] start repair l%d :'%(fidx, lemmaIdx) , lemma.serialize())
                
            # or it is in the fact
            # then we know this lemma is a bad one
            # so let's repair it

            # IMPROVEMENT: variable set change below

            opextract = OpExtractor() # work on itp 
            opextract.walk(lemma)
            lemma_var_set = opextract.Symbols
            post_ex_var_set = _get_var(post_ex)

            inv_var_set = lemma_var_set.union(post_ex_var_set)
            sorted_inv_var_set = sorted(list(inv_var_set), key = lambda x: x.symbol_name())
            # IMPROVEMENT: this is not right!!!
            
            # cexIdxs

            blocked_cexs = self.cexs_blocked.get(fidx,[]) # fidx+1 is fewer cex
            facts = self.unblockable_fact[fidx+1]         # facts should be more facts
            facts_on_inv_vars = _get_cubes_with_more_var(facts, inv_var_set) # and will shrink var

            # IMPROVEMENT: you may not want to use all cex, 
            # 1. probably just the unblocked ones
            # 2. probably just the one it blocks
            # 3. probably rule out those that are hard to block...
            # 4. probably you can try many different times with different ...
            # 5. but facts must be taken into consideration any way!!!
            cexs_on_inv_vars, blocked_c_idxs = self.shrink_var_cexs(cexs = blocked_cexs, \
                cex_picks = cexIdxs,
                fidx = fidx + 1, varset = inv_var_set, \
                remove_vars = remove_vars, keep_vars = keep_vars) 
            #cexs_on_inv_vars = _get_cubes_with_fewer_var(blocked_cexs, inv_var_set)
            sorted_allvars = sorted(self.system.variables, key = lambda x: x.symbol_name())
            sorted_prime_vars = sorted(self.system.prime_variables, key = lambda x: x.symbol_name())

            self.dump_frames()
            print ('  [push_lemma F%d] Invoke SyGuS Now:'%(fidx))
            print ('----------------\nvarset:\n',inv_var_set)
            print ('----------------\ncex:\n',   cexs_on_inv_vars)
            print ('----------------\nfacts:\n', facts_on_inv_vars)
            if (len(cexs_on_inv_vars) == 0 or len(facts_on_inv_vars) == 0):
                print ('  [push_lemma F%d] WARNING: no cex! skip sygus'%(fidx))
                input ()
                continue



            cex_guided_pbe = CexGuidedPBE( \
                primal_vars = self.system.variables,
                prime_vars  = self.system.prime_variables,
                primal_map  = self.primal_map, # next_v --> v
                prime_map   = self.prime_map, # v --> next_v
                T =  self.system.trans,
                F_idx_minus2 =  self.frames[fidx],
                Init = self.system.init, # IMPROVEMENT: Use init
                inv_var_set = inv_var_set, # we can change this if necessary
                facts_on_inv_vars = facts_on_inv_vars,
                cexs_on_inv_vars = cexs_on_inv_vars,
                sorted_inv_var_set = sorted_inv_var_set,
                sorted_allvars = sorted_allvars,
                sorted_prime_vars = sorted_prime_vars,
                op_obj = opextract \
                )

            # lemma /\ F /\ T => lemma'
            itp = cex_guided_pbe.syn_lemma_F_T_implies_lemma_prime(fidx = fidx, lidx = lemmaIdx, itp = lemma, \
                frame_dump = self.dump_frames(toStr = True))

            if itp is None:
                print ('  [push_lemma F%d] Repair lemma l%d failed: ' % (fidx, lemmaIdx))
                if len(cexIdxs) == 1:
                    for cidx in cexIdxs:
                        hashkey = self._canonicalize_cex( self.cexs_blocked[fidx][cidx] )
                        n_fail, n_total = self.cex_to_itp_enhance_fail.get(hashkey, (0,0))
                        self.cex_to_itp_enhance_fail[hashkey] = (n_fail+1, n_total+1)
                continue # syn failed: try next

            itp_prime_var = itp.substitute(cex_guided_pbe.prime_map)
            #md = self.solve(Not(Implies(And(self.frames[fidx] + [self.system.trans, itp]), itp_prime_var ) ) )
            #if md is not None:
            #    print (md)

            # assert (init -> lemma)
            assert (self.solve(Not(Implies(self.system.init, itp))) is None)
            # assert (lemma /\ F /\ T => lemma')
            assert (self.solve(Not(Implies(And(self.frames[fidx] + [self.system.trans, itp]), itp_prime_var ) ) ) is None )
            # if not (F[fidx-1]) => itp
            #   add to all previous frames
            self._add_lemma(lemma = itp, fidx = fidx+1, cidxs = ???) # checks its cexs next level cexIdx : blocked_c_idxs

            # deal with cex_covered_by_newly_pushed_lemmas
            blocked_cex_in_prev_frame = set()
            for cIdx in blocked_c_idxs:
                ??? will also need to change ???
                prev_cex_idx = self.cex_origin.get(fidx, dict()).get(cIdx, None)
                # if it has an origin
                if isinstance(prev_cex_idx,int):
                    blocked_cex_in_prev_frame.add( prev_cex_idx )

            self.lemma_to_cex_map_perframe[fidx][lemmaIdx] = self.lemma_to_cex_map_perframe[fidx].get(lemmaIdx, set()).union(\
                blocked_cex_in_prev_frame) # update the current lemma as it blocks a lot more now than it was
            self.cex_covered_by_pushed_lemmas[fidx] = self.cex_covered_by_pushed_lemmas.get(fidx,set()).union(\
                blocked_cex_in_prev_frame) # and now we have some more covered

            #if (self.solve(Not(Implies(And(self.frames[fidx-1]), itp))) is not None):
            print ('  [push_lemma F%d] Add to all prev frame '%(fidx) )
            self.frames[fidx][lemmaIdx] = And(lemma, itp) # we don't want to touch the lemma Idx will mess things up
            self._add_lemma_to_all_prev_frame(end_frame_id = fidx-1, lemma = itp)
            # end of the for loop for repairing lemmas

        self.frames_pushed_idxs_map[fidx] =  end_lemma_idx
        # if len(self.frames[fidx]) > end_lemma_idx : we have unpushed lemmas
        # how hard to try?
        print ('  [push_lemma F%d] push lemma finished, press any key to continue'%fidx)
        pause()

