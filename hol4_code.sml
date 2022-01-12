app load ["arithmeticTheory", "realTheory", "prim_recTheory", "seqTheory",
          "pred_setTheory","res_quanTheory", "res_quanTools", "listTheory", "probabilityTheory", "numTheory", "dep_rewrite", 
          "transcTheory", "rich_listTheory", "pairTheory",
          "combinTheory","limTheory","sortingTheory", "realLib", "optionTheory","satTheory",
          "util_probTheory", "extrealTheory", "measureTheory", "lebesgueTheory","real_sigmaTheory"];

open HolKernel Parse boolLib bossLib limTheory arithmeticTheory realTheory prim_recTheory probabilityTheory
     seqTheory pred_setTheory res_quanTheory sortingTheory res_quanTools listTheory transcTheory
     rich_listTheory pairTheory combinTheory realLib  optionTheory dep_rewrite
      util_probTheory extrealTheory measureTheory lebesgueTheory real_sigmaTheory satTheory numTheory;

open HolKernel boolLib bossLib Parse;
(*** C-u C-u M-h M-r ***)
(***************************)
(*** GENERAL DEFINITIONS ***)
(***************************) 

(********* X <= Y **********)
val X_LOW_Y_def=Define
 `(X_LOW_Y [] [] = T) /\
  (X_LOW_Y  (L:num list) [] = F) /\
  (X_LOW_Y [] (L:num list) = F) /\
  (X_LOW_Y (hx:num::tx) (hy:num::ty) = (hx<=hy) /\ (X_LOW_Y tx ty))`;
(********* X \/ Y *******)
val X_OR_Y_def=Define
 `(X_OR_Y ([]:(num#num) list) = []) /\
  (X_OR_Y (h:num#num::t)  = (MAX (FST h) (SND h)) :: (X_OR_Y t))`;
(********* X /\ Y *******)
val X_AND_Y_def=Define
 `(X_AND_Y ([]:(num#num) list) = []) /\
  (X_AND_Y (h:num#num::t)  = (MIN (FST h) (SND h)) :: (X_AND_Y t))`;
(**********X < Y*********)
val X_LOWER_Y_def=Define
 `(X_LOWER_Y ([]:(num#num) list) = T) /\
  (X_LOWER_Y (h:num#num::t)  = ((FST h) < (SND h)) /\ (X_LOWER_Y t))`;

val X_SAME_Y_def=Define
 `(X_SAME_Y [] [] = T) /\
  (X_SAME_Y (hx::tx) (hy::ty) = (hx=hy) /\ (X_SAME_Y tx ty))`;
(************ Pair List********)
val X_list_def=Define
`(X_list [] = []) /\
 (X_list (h:'a#'b::t) =  (FST h)::X_list t)`;
val Y_list_def=Define
`(Y_list [] = []) /\
 (Y_list (h:'a#'b::t) =  SND h :: Y_list t)`;

 (*** UPPER BOUND **)
val max_vec_def=Define
`(max_vec [] = 0) /\
 (max_vec [x:num]  = x) /\
 (max_vec  ((h:num)::x) = MAX h (max_vec x)) `;
(*** LOWER BOUND***)
 val min_vec_def=Define
`(min_vec [] = 0) /\
 (min_vec [x:num]  = x) /\
 (min_vec  ((h:num)::x) = MIN h (min_vec x)) `; 
(*************************************)
(*********** SERIES SYSTEM ***********)
(*************************************)
val series_MS_def = Define
 `(series_MS [] = (0:num)) /\ 
  (series_MS [x] = x:num) /\
  (series_MS (x:num::xs) = MIN x (series_MS xs))`;
(********P1********) 
g `!(L:(num#num) list). ~NULL L /\  X_LOW_Y (X_list L) (Y_list L) ==>
  (series_MS (X_list L) <= series_MS (Y_list L))`;
e(GEN_TAC);
e(Induct_on`L`);
 e(RW_TAC list_ss[NULL]);
 e(RW_TAC std_ss[series_MS_def,X_LOW_Y_def,X_list_def,Y_list_def]);
 e(FULL_SIMP_TAC list_ss[series_MS_def,X_LOW_Y_def,X_list_def,Y_list_def]);
 e(Cases_on`L`);
   e(FULL_SIMP_TAC list_ss[series_MS_def,X_LOW_Y_def,X_list_def,Y_list_def]);
   e(FULL_SIMP_TAC list_ss[series_MS_def,X_LOW_Y_def,X_list_def,Y_list_def]);
val PHI_LOWER=top_thm();
(******P2********)
g`!L j. ~NULL L /\ (!x. MEM x L ==>  (x = j)) ==> (series_MS L = j)`;
e(REPEAT GEN_TAC);
e(Induct_on`L`);
  e(RW_TAC std_ss[series_MS_def,MEM,NULL]);
  e(RW_TAC std_ss[] THEN FULL_SIMP_TAC std_ss[NULL,MEM]);
  e(Cases_on`L`);
	e(FULL_SIMP_TAC std_ss[series_MS_def,NULL,MEM]); 
  	e(FULL_SIMP_TAC std_ss[series_MS_def,NULL,MEM]);
(******* P3 ******)
(**LEMMA**)
g`!h h' L. (series_MS (h::h'::L)) = (series_MS (h'::h::L))`;
e(Induct_on`L`);
e(RW_TAC std_ss[MIN_COMM,series_MS_def]);
e(RW_TAC std_ss[series_MS_def,MIN_ASSOC,MIN_COMM]);
e(FULL_SIMP_TAC std_ss[series_MS_def,GSYM MIN_ASSOC]);
val COMM_SER_HH=top_thm();
(***Main P3***)
g `!l j L i. l<>j /\ i< LENGTH L /\ ~NULL L /\ (!x. MEM x L ==> (x > j)) /\ ((series_MS (LUPDATE j i L))=j) ==> 
( (series_MS (LUPDATE l i L)) <> j )`;
e(Induct_on`L`);
e(FULL_SIMP_TAC list_ss[]);
e(Cases_on`i`);
e(EVAL_TAC);
e(Cases_on`L`);
e(FULL_SIMP_TAC list_ss[series_MS_def]);
e(ONCE_REWRITE_TAC[COMM_SER_HH]);
e(REPEAT GEN_TAC);
e(FIRST_X_ASSUM (MP_TAC o Q.SPECL [`l`,`j`,`0`]));
e(EVAL_TAC);
e(RW_TAC std_ss[]);
e(POP_ASSUM MP_TAC);
e(FULL_SIMP_TAC std_ss[MEM,DISJ_IMP_THM]);
e(FIRST_X_ASSUM (MP_TAC o Q.SPECL [`h`]));
e(FULL_SIMP_TAC std_ss[MEM,DISJ_IMP_THM,MIN_DEF]);
e(RW_TAC real_ss[]); 
e(RW_TAC std_ss[LUPDATE_def,NULL,MEM,LENGTH]);
 e(Cases_on`L`);
 e(FULL_SIMP_TAC std_ss[LUPDATE_def,NULL,series_MS_def,LENGTH]);
 e(Cases_on`n`);
 e(FIRST_X_ASSUM (MP_TAC o Q.SPECL [`l`,`j`,`0`]));
 e(FULL_SIMP_TAC std_ss[LUPDATE_def,NULL,series_MS_def,LENGTH,MEM,DISJ_IMP_THM,MIN_DEF]);
 e(FIRST_X_ASSUM (MP_TAC o Q.SPECL [`h`]));
 e(POP_ASSUM MP_TAC);
 e(RW_TAC real_ss[]);
 e(FIRST_X_ASSUM (MP_TAC o Q.SPECL [`l`,`j`,`SUC n'`]));
 e(FULL_SIMP_TAC std_ss[LUPDATE_def,series_MS_def,NULL,MEM,MIN_DEF,DISJ_IMP_THM]);
 e(FIRST_X_ASSUM (MP_TAC o Q.SPECL [`h`]));
 e(FULL_SIMP_TAC real_ss[MEM,MIN_DEF]);
(************TH3.1 SERIES************)
g`!X. min_vec X <= series_MS X /\ series_MS X <= max_vec X`;
e(Induct_on`X`);
e(fs[min_vec_def,max_vec_def,series_MS_def]);
e(Cases_on`X`);
e(fs[min_vec_def,max_vec_def,series_MS_def]);
e(fs[min_vec_def,max_vec_def,series_MS_def]);
(************TH3.2 (i) SERIES************)
g`!L. series_MS (X_OR_Y L) >= MAX (series_MS (X_list L)) (series_MS (Y_list L))`;
e(Induct_on`L`);
 e(fs[X_OR_Y_def,Y_list_def,X_list_def,series_MS_def,FST,SND]);
e(Cases_on`L`);
 e(fs[X_OR_Y_def,Y_list_def,X_list_def,series_MS_def,FST,SND]);
  e(fs[X_OR_Y_def,Y_list_def,X_list_def,series_MS_def,FST,SND,MIN_DEF,MAX_DEF]);
(************TH3.2 (ii) SERIES************)
g`!L. series_MS (X_AND_Y L) <= MIN (series_MS (X_list L)) (series_MS (Y_list L))`;
e(Induct_on`L`);
 e(fs[X_AND_Y_def,Y_list_def,X_list_def,series_MS_def,FST,SND]);
e(Cases_on`L`);
 e(fs[X_AND_Y_def,Y_list_def,X_list_def,series_MS_def,FST,SND]);
  e(fs[X_AND_Y_def,Y_list_def,X_list_def,series_MS_def,FST,SND,MIN_DEF,MAX_DEF]);

(************************************************)
(******* TH3.3  DEFINITIONS and LEMMAS **********)
(************************************************)
(********** DEFs ************)
val con_vec_def=Define
`con_vec X j PHI = ((PHI X) = j:num)`;
val uc_con_vec_def=Define
`uc_con_vec X j PHI = 
 (con_vec X j PHI)  /\ !Y. (X_LOWER_Y (ZIP (Y,X))) ==> (PHI Y < j)`; 
val uc_con_vec_set0_def = Define
`(uc_con_vec_set0 (0:num) Y j PHI = uc_con_vec (Y 0) j PHI) /\
 (uc_con_vec_set0 (SUC n) Y j PHI =
  uc_con_vec (Y (SUC n)) j PHI /\ uc_con_vec_set0 n Y j PHI)`;
(************* LEMMAS *********)
  g`!Y l L. (Y l = X_list L) /\(X_LOW_Y (Y l) (Y_list L)) ==> X_LOW_Y (X_list L) (Y_list L)`;
e(Induct_on`L`);
e(fs[X_LOW_Y_def,X_list_def,Y_list_def]);
e(rw[]);
e(Cases_on`(Y l)`);
e(REPEAT(POP_ASSUM MP_TAC) THEN rw[]);
e(REPEAT(POP_ASSUM MP_TAC) THEN rw[]);
val XLOWY_T1=top_thm();
g`!t X. (LENGTH (t:num list) = LENGTH (X:num list)) ==> ((X_list (ZIP (t,X))) = t)`;
e(Induct_on`X`);
e(rw[LENGTH_NIL,X_list_def]);
e(Cases_on`t`);
e(fs[LENGTH]);
e(fs[LENGTH,X_list_def]);
val X_list_ZIP=top_thm(); 

g`!t X.(LENGTH (t:num list) = LENGTH (X:num list)) ==> ((Y_list (ZIP (t,X))) = X)`;
e(Induct_on`X`);
e(rw[LENGTH_NIL,Y_list_def]);
e(Cases_on`t`);
e(fs[LENGTH]);
e(fs[LENGTH,Y_list_def]);
val Y_list_ZIP=top_thm();

g`!Y n j PHI. uc_con_vec_set0 n Y j PHI ==> (PHI (Y n) = j)`;
e(Induct_on`n` THEN rw[uc_con_vec_set0_def,uc_con_vec_def,con_vec_def]);
val SEN_T2=top_thm();

g`!Y j l n PHI. uc_con_vec_set0 n Y j PHI /\ (l<=n) ==> uc_con_vec_set0 l Y j PHI`;
e(Induct_on`l`);
  e(Induct_on`n`);
  e(rw[]);
  e(rw[uc_con_vec_set0_def]);
  e(rw[]);
  e(Induct_on`n`);
  e(rw[]);
  e(FIRST_X_ASSUM (MP_TAC o Q.SPECL [`Y`,`j`,`n`]) THEN rw[]);
  e(KNOW_TAC``uc_con_vec_set0 n Y j PHI``);
  e(fs[uc_con_vec_set0_def]);
  e(REPEAT(POP_ASSUM MP_TAC) THEN fs[GSYM LESS_EQ]);
  e(rw[] THEN fs[]);
  e(KNOW_TAC``(l=n:num) \/(l<n)``); 
  e(fs[]);
  e(fs[DISJ_IMP_THM]);
val THS1=top_thm(); 
(******** TH3.3 SERIES ***********)
g`!n Y j l X. ~NULL (X) /\ ((LENGTH (Y l)) = (LENGTH X))  /\  uc_con_vec_set0 n Y j series_MS ∧
       X_LOW_Y (Y l) X ∧ n ≥ l ⇒
       (series_MS X ≥ j)`;
e(fs[GREATER_EQ]);
e(Induct_on`X` THEN rw[]);
e(Cases_on`(Y l)`);
e(fs[LENGTH]);
e(KNOW_TAC``j = series_MS (h'::t)``);
e(KNOW_TAC``!Y n j. uc_con_vec_set0 n Y j series_MS ==> (series_MS (Y n) = j)``);
 e(fs[SEN_T2]); 
e(rw[]);
e(KNOW_TAC`` uc_con_vec_set0 l Y j series_MS``);
e(MATCH_MP_TAC THS1);
e(EXISTS_TAC(--`n:num`--));
e(fs[]);
e(FIRST_X_ASSUM (MP_TAC o Q.SPECL [`Y`,`l`, `j`]));
e(REPEAT(POP_ASSUM MP_TAC));
e(rw[]);
e(rw[]);
e(fs[LENGTH]);
e(KNOW_TAC``!(L:(num#num) list). ~NULL L /\  X_LOW_Y (X_list L) (Y_list L) ==>
  (series_MS (X_list L) <= series_MS (Y_list L))``);
e(fs[PHI_LOWER]);
e(rw[]);
e(FIRST_X_ASSUM (MP_TAC o Q.SPECL [`ZIP((h':num::t),(h:num::X))`]));
e(KNOW_TAC``((Y_list (ZIP (t,X))) = (X:num list)) /\  ((X_list (ZIP (t,X))) =  (t:num list))``);
e(rw[]);
e(MATCH_MP_TAC Y_list_ZIP);
e(rw[]);
e(MATCH_MP_TAC X_list_ZIP);
e(rw[]);
 e(fs[X_LOW_Y_def,X_list_def,Y_list_def]);
(********************************)
(********************************)

(********************************)
(********* PARALLEL SYSTEM ******)
(********************************)
val parallel_MS_def = Define
 `(parallel_MS [] = (0:num)) /\ 
  (parallel_MS [x] = x:num) /\
  (parallel_MS (x:num::xs) = MAX x (parallel_MS xs))`;
(********P1*************)
g `!(L:(num#num) list). ~NULL L /\  X_LOW_Y (X_list L) (Y_list L) ==>
  (parallel_MS (X_list L) <= parallel_MS (Y_list L))`;
e(GEN_TAC);
e(Induct_on`L`);
 e(RW_TAC list_ss[NULL]);
 e(RW_TAC std_ss[parallel_MS_def,X_LOW_Y_def,X_list_def,Y_list_def]);
 e(FULL_SIMP_TAC list_ss[parallel_MS_def,X_LOW_Y_def,X_list_def,Y_list_def]);
 e(Cases_on`L`);
   e(FULL_SIMP_TAC list_ss[parallel_MS_def,X_LOW_Y_def,X_list_def,Y_list_def]);
   e(FULL_SIMP_TAC list_ss[parallel_MS_def,X_LOW_Y_def,X_list_def,Y_list_def]);
   val PHI_LOWER2=top_thm();
(******P2********)
g`!L j. ~NULL L /\ (!x. MEM x L ==>  (x = j)) ==> (parallel_MS L = j)`;
e(REPEAT GEN_TAC);
e(Induct_on`L`);
  e(RW_TAC std_ss[parallel_MS_def,MEM,NULL]);
  e(RW_TAC std_ss[] THEN FULL_SIMP_TAC std_ss[NULL,MEM]);
  e(Cases_on`L`);
	e(FULL_SIMP_TAC std_ss[parallel_MS_def,NULL,MEM]); 
  	e(FULL_SIMP_TAC std_ss[parallel_MS_def,NULL,MEM]);
(*******P3********)
(***LEMMA*****)
g`!h h' L. (parallel_MS (h::h'::L)) = (parallel_MS (h'::h::L))`;
e(Induct_on`L`);
e(RW_TAC std_ss[MAX_COMM,parallel_MS_def]);
e(RW_TAC std_ss[parallel_MS_def,MAX_ASSOC,MAX_COMM]);
e(FULL_SIMP_TAC std_ss[parallel_MS_def,GSYM MAX_ASSOC]);
val COMM_PAR_HH=top_thm();
(****Main P3P****)
g `!l j L i. l<>j /\ i< LENGTH L /\ ~NULL L /\ (!x. MEM x L ==> (x < j)) /\ ((parallel_MS (LUPDATE j i L))=j) ==> 
( (parallel_MS (LUPDATE l i L)) <> j )`;
e(Induct_on`L`);
e(FULL_SIMP_TAC list_ss[]);
e(Cases_on`i`);
e(EVAL_TAC);
e(Cases_on`L`);
e(FULL_SIMP_TAC list_ss[parallel_MS_def]);
e(ONCE_REWRITE_TAC[COMM_PAR_HH]);
e(REPEAT GEN_TAC);
e(FIRST_X_ASSUM (MP_TAC o Q.SPECL [`l`,`j`,`0`]));
e(EVAL_TAC);
e(RW_TAC std_ss[]);
e(POP_ASSUM MP_TAC);
e(FULL_SIMP_TAC std_ss[MEM,DISJ_IMP_THM]);
e(FIRST_X_ASSUM (MP_TAC o Q.SPECL [`h`]));
e(FULL_SIMP_TAC std_ss[MEM,DISJ_IMP_THM,MAX_DEF]);
e(RW_TAC real_ss[]); 
e(RW_TAC std_ss[LUPDATE_def,NULL,MEM,LENGTH]);
 e(Cases_on`L`);
 e(FULL_SIMP_TAC std_ss[LUPDATE_def,NULL,parallel_MS_def,LENGTH]);
 e(Cases_on`n`);
 e(FIRST_X_ASSUM (MP_TAC o Q.SPECL [`l`,`j`,`0`]));
 e(FULL_SIMP_TAC std_ss[LUPDATE_def,NULL,parallel_MS_def,LENGTH,MEM,DISJ_IMP_THM,MAX_DEF]);
 e(FIRST_X_ASSUM (MP_TAC o Q.SPECL [`h`]));
 e(POP_ASSUM MP_TAC);
 e(RW_TAC real_ss[]);
 e(FIRST_X_ASSUM (MP_TAC o Q.SPECL [`l`,`j`,`SUC n'`]));
 e(FULL_SIMP_TAC std_ss[LUPDATE_def,parallel_MS_def,NULL,MEM,MAX_DEF,DISJ_IMP_THM]);
 e(FIRST_X_ASSUM (MP_TAC o Q.SPECL [`h`]));
 e(FULL_SIMP_TAC real_ss[MEM,MAX_DEF]);

(************TH3.1 PARALLEL ************)
g`!X. min_vec X <= parallel_MS X /\ parallel_MS X <= max_vec X`;
e(Induct_on`X`);
e(fs[min_vec_def,max_vec_def,parallel_MS_def]);
e(Cases_on`X`);
e(fs[min_vec_def,max_vec_def,parallel_MS_def]);
e(fs[min_vec_def,max_vec_def,parallel_MS_def]);
(************TH3.2 (i) PARALLEL ************)
g`!L. parallel_MS (X_OR_Y L) >= MAX (parallel_MS (X_list L)) (parallel_MS (Y_list L))`;
e(Induct_on`L`);
 e(fs[X_OR_Y_def,Y_list_def,X_list_def,parallel_MS_def,FST,SND]);
e(Cases_on`L`);
 e(fs[X_OR_Y_def,Y_list_def,X_list_def,parallel_MS_def,FST,SND]);
  e(fs[X_OR_Y_def,Y_list_def,X_list_def,parallel_MS_def,FST,SND,MIN_DEF,MAX_DEF]);
(************TH3.2 (ii) PARALLEL ************)
g`!L. parallel_MS (X_AND_Y L) <= MIN (parallel_MS (X_list L)) (parallel_MS (Y_list L))`;
e(Induct_on`L`);
 e(fs[X_AND_Y_def,Y_list_def,X_list_def,parallel_MS_def,FST,SND]);
e(Cases_on`L`);
 e(fs[X_AND_Y_def,Y_list_def,X_list_def,parallel_MS_def,FST,SND]);
  e(fs[X_AND_Y_def,Y_list_def,X_list_def,parallel_MS_def,FST,SND,MIN_DEF,MAX_DEF]);
(******** TH3.3 PARALLEL *********)
g`!n Y j l X. ~NULL (X) /\ ((LENGTH (Y l)) = (LENGTH X))  /\  uc_con_vec_set0 n Y j parallel_MS ∧
       X_LOW_Y (Y l) X ∧ n ≥ l ⇒
       (parallel_MS X ≥ j)`;
e(fs[GREATER_EQ]);
e(Induct_on`X` THEN rw[]);
e(Cases_on`(Y l)`);
e(fs[LENGTH]);
e(KNOW_TAC``j = parallel_MS (h'::t)``);
e(KNOW_TAC``!Y n j. uc_con_vec_set0 n Y j parallel_MS ==> (parallel_MS (Y n) = j)``);
 e(fs[SEN_T2]); 
 e(rw[]);
e(KNOW_TAC`` uc_con_vec_set0 l Y j parallel_MS``);
e(MATCH_MP_TAC THS1);
e(EXISTS_TAC(--`n:num`--));
e(fs[]);
e(FIRST_X_ASSUM (MP_TAC o Q.SPECL [`Y`,`l`, `j`]));
e(REPEAT(POP_ASSUM MP_TAC));
e(rw[]);
e(rw[]);
e(fs[LENGTH]);
e(KNOW_TAC``!(L:(num#num) list). ~NULL L /\  X_LOW_Y (X_list L) (Y_list L) ==>
  (parallel_MS (X_list L) <= parallel_MS (Y_list L))``);
e(fs[PHI_LOWER2]);
e(rw[]);
e(FIRST_X_ASSUM (MP_TAC o Q.SPECL [`ZIP((h':num::t),(h:num::X))`]));
e(KNOW_TAC``((Y_list (ZIP (t,X))) = X:num list) /\  ((X_list (ZIP (t,X))) = t:num list)``);
e(rw[]);
e(MATCH_MP_TAC Y_list_ZIP);
e(rw[]);
e(MATCH_MP_TAC X_list_ZIP);
e(rw[]);
 e(fs[X_LOW_Y_def,X_list_def,Y_list_def]);
(***************************************)
 
(*****************************************)
(****** THE COMPONENT MODELING ***********)
(*****************************************)

val perf_event_comp_def = Define
`perf_event_comp X p j = {x | (X x) = j:num} INTER p_space p`;

val perf_dist_event_comp_def = Define
`perf_dist_event_comp X p j = {x | (X x) <= j:num} INTER p_space p`;

val perf_union_event_list_def= Define
`(perf_union_event_list X p 0 = perf_event_comp X p 0) /\
 (perf_union_event_list X p (SUC n) = (perf_event_comp X p (SUC n)) UNION (perf_union_event_list X p n) )`;
 
val perf_comp_MS_def =Define
 `perf_comp_MS X p = \a. prob p (perf_event_comp X p a)`;
 
val perf_dist_comp_MS_def =Define
 `perf_dist_comp_MS X p = \a.prob p (perf_dist_event_comp X p a)`;

val compl_perf_dist_comp_MS_def= Define
`compl_perf_dist_comp_MS X p = (\a. (1 - perf_dist_comp_MS X p a))`;

val perf_comp_MS_State_SUM_def =Define
 `(perf_comp_MS_State_SUM X p 0 = prob p (perf_event_comp X p 0)) /\ 
  (perf_comp_MS_State_SUM X p (SUC l) = (prob p (perf_event_comp X p (SUC l)))+ (perf_comp_MS_State_SUM X p l))`;
  
val comp_events_space_def=Define
`(comp_events_space X 0 = (PREIMAGE X {0})) /\
 (comp_events_space X (SUC M) = (PREIMAGE X {SUC M}) UNION  (comp_events_space X M) )`;
   
g`!X p l. perf_dist_event_comp X p l = perf_union_event_list X p l`;
e(Induct_on`l`);
e(EVAL_TAC THEN rw[]);
e(rw[] THEN FIRST_X_ASSUM (MP_TAC o Q.SPECL [`X`,`p`]));
e(fs[perf_union_event_list_def,perf_event_comp_def,perf_dist_event_comp_def,EQ_SYM_EQ]);
e(EVAL_TAC THEN fs[SUBSET_DEF]);
val CDF_PMF_list=top_thm();

g`!x X p l.  (({x | X x = SUC l} INTER p_space p) UNION (perf_dist_event_comp X p l)) = (perf_dist_event_comp X p (SUC l))`;
e(EVAL_TAC THEN fs[perf_dist_event_comp_def,SUBSET_DEF,UNION_DEF]);
val CDF_SUC_UNION=top_thm();

 g`!A B C. A INTER B INTER (A INTER C) = A INTER ( B INTER C)`;
 e(rw[INTER_DEF]);
 e(KNOW_TAC``!A B C. ((A /\ B ) /\ A /\ C) = (A /\ B /\ C)``);
 e(DECIDE_TAC);
 e(rw[]);
 val INTER_ABC=top_thm();

 g`!X x j. DISJOINT ({x | X x = (SUC j)} INTER p_space p) (perf_dist_event_comp X p j)`;
 e(rw[DISJOINT_DEF,perf_dist_event_comp_def,INTER_COMM,INTER_ABC] THEN fs[INTER_DEF]);
 val CDF_SUC_DISJOINT=top_thm();
 
 g`!X p j. (prob_space p) /\ (!l. (perf_event_comp X p l) IN events p) ==> ( (perf_dist_event_comp X p j) IN events p)`;
 e(fs[CDF_PMF_list]);
 e(Induct_on`j`);
 e(fs[perf_union_event_list_def,perf_event_comp_def]);
 e(rw[] THEN FIRST_X_ASSUM (MP_TAC o Q.SPECL [`X`,`p`]));
 e(fs[perf_union_event_list_def,EVENTS_UNION]);
 val CDF_EVENTS_UNION=top_thm();
 
g`!X p j. (prob_space p) /\ (!l. (perf_event_comp X p l) IN events p) ==> (perf_dist_comp_MS X p j = perf_comp_MS_State_SUM X p j)`; 
e(Induct_on`j`);
e(EVAL_TAC THEN fs[]);
e(rw[] THEN FIRST_X_ASSUM (MP_TAC o Q.SPECL [`X`,`p`]) THEN rw[perf_dist_comp_MS_def,perf_comp_MS_State_SUM_def]);
e(fs[EQ_SYM_EQ] THEN MATCH_MP_TAC PROB_ADDITIVE);
e(fs[CDF_SUC_UNION,CDF_SUC_DISJOINT,perf_event_comp_def,CDF_EVENTS_UNION]);
val CDF_PMF_comp1=top_thm();


g`!M X. comp_events_space X M = {x| X x <= M}`;
e(Induct_on`M` THEN fs[comp_events_space_def,PREIMAGE_def,LE_SUC,UNION_DEF,DISJ_COMM]);
val PREIM_X_SET=top_thm();

g`!X p sp M. (prob_space p) /\(comp_events_space X M = p_space p)  
      ==> (perf_dist_comp_MS X p M = 1)`;
e(Induct_on`M`);
e(fs[perf_dist_comp_MS_def,perf_dist_event_comp_def,comp_events_space_def,PREIMAGE_def,PROB_SPACE]);
e(fs[perf_dist_comp_MS_def,perf_dist_event_comp_def,comp_events_space_def,PREIMAGE_def,LE_SUC,PROB_SPACE,PREIM_X_SET,DISJ_COMM,UNION_DEF]);

(*********************************************)
(********* SYSTEM MODELING (p_space) *********)
(*********************************************)
val perf_sys_event_MS_def = Define
`perf_sys_event_MS (PHI:num list -> num) X p j = 
         {x | PHI (MAP (\a. a x) X) = j:num} INTER p_space p`;

val perf_dist_sys_event_MS_def = Define
`perf_dist_sys_event_MS (PHI:num list -> num) X p j =
         {x | PHI (MAP (\a. a x) X) <= j:num} INTER p_space p`;

val perf_sys_MS_def =Define
 `perf_sys_MS PHI X p = \a. prob p (perf_sys_event_MS PHI X p a)`;

val perf_sys_MS_cumsum_def=Define
`(perf_sys_MS_cumsum PHI X p 0 = perf_sys_MS PHI X p 0) /\
 (perf_sys_MS_cumsum PHI X p (SUC j) =(perf_sys_MS_cumsum PHI X p j)+(perf_sys_MS PHI X p (SUC j)))`;

val perf_dist_sys_MS_def =Define
 `perf_dist_sys_MS PHI X p = \a. prob p (perf_dist_sys_event_MS PHI X p a)`;
 
val perf_sys_MS_union_events_def=Define
`(perf_sys_MS_union_events PHI X p 0 = perf_sys_event_MS PHI X p 0) /\
 (perf_sys_MS_union_events PHI X p (SUC j) = (perf_sys_event_MS PHI X p (SUC j))  UNION (perf_sys_MS_union_events PHI X p j))`;
 
val compl_perf_dist_sys_MS_def= Define
`compl_perf_dist_sys_MS PHI X p = (\a. (1 - perf_dist_sys_MS PHI X p a))`;



g`!X p j.(perf_dist_sys_event_MS series_MS X p j = perf_sys_MS_union_events series_MS X p j)`; 
e(REPEAT(GEN_TAC) THEN ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN Induct_on`j`);
e(EVAL_TAC THEN rw[]);
e(fs[perf_sys_MS_union_events_def]);(* THEN FIRST_X_ASSUM (MP_TAC o Q.SPECL [`X`]));*)
e(EVAL_TAC THEN fs[UNION_DEF,SUBSET_DEF]);
val CDF_PMF_SER_event=top_thm();

g`!X p j. (perf_dist_sys_event_MS parallel_MS X p j = perf_sys_MS_union_events parallel_MS X p j)`; 
e(REPEAT(GEN_TAC) THEN ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN Induct_on`j`);
e(EVAL_TAC THEN rw[]);
e(fs[perf_sys_MS_union_events_def]);(* THEN FIRST_X_ASSUM (MP_TAC o Q.SPECL [`X`]));*)
e(EVAL_TAC THEN fs[UNION_DEF,SUBSET_DEF]);
val CDF_PMF_PAR_event=top_thm();

g`!X PHI p j. (perf_dist_sys_event_MS PHI X p j = perf_sys_MS_union_events PHI X p j)`; 
e(REPEAT(GEN_TAC) THEN ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN Induct_on`j`);
e(EVAL_TAC THEN rw[]);
e(fs[perf_sys_MS_union_events_def]);(* THEN FIRST_X_ASSUM (MP_TAC o Q.SPECL [`X`]));*)
e(EVAL_TAC THEN fs[UNION_DEF,SUBSET_DEF]);
val CDF_PMF_PHI_event=top_thm();

g`!X PHI p j. (prob_space p) /\ (!l. (perf_sys_event_MS PHI X p l) IN events p) ==> 
     (perf_dist_sys_event_MS PHI X p j IN events p)`;
e(fs[CDF_PMF_PHI_event]);
e(Induct_on`j` THEN rw[perf_sys_MS_union_events_def,EVENTS_UNION]);
val CDF_EVENTS_UNION_PHI=top_thm();

(**(prob_space p) /\ (!l. (perf_event_comp X l) IN events p)**)

g`!X PHI p j. (prob_space p) /\ (!l. (perf_sys_event_MS PHI X p l) IN events p) ==> 
     (perf_dist_sys_MS PHI X p j = perf_sys_MS_cumsum PHI X p j)`;
e(Induct_on`j`);
e(fs[perf_dist_sys_MS_def,perf_sys_MS_cumsum_def,perf_sys_MS_def,perf_dist_sys_event_MS_def,perf_sys_event_MS_def]);
e(rw[perf_sys_MS_cumsum_def] THEN FIRST_X_ASSUM (MP_TAC o Q.SPECL [`X`,`PHI`,`p`])); 
e(fs[perf_dist_sys_MS_def,EQ_SYM_EQ]);
e(rw[perf_sys_MS_def] THEN MATCH_MP_TAC PROB_ADDITIVE);
e(fs[CDF_EVENTS_UNION_PHI,CDF_PMF_PHI_event,perf_sys_MS_union_events_def,UNION_COMM]);
 e(fs[DISJOINT_DEF,GSYM CDF_PMF_PHI_event,perf_sys_event_MS_def,perf_dist_sys_event_MS_def,INTER_COMM,INTER_ABC]);
 e(fs[INTER_DEF]);

g`!X p j. ~NULL (X) ==> ((perf_dist_sys_event_MS series_MS X p j) = (BIGUNION(set (MAP (\a.(perf_dist_event_comp a p j)) X)))) `;
e(Induct_on`X` THEN rw[]);
e(Cases_on`X`);
e(fs[perf_dist_sys_event_MS_def,series_MS_def,perf_dist_event_comp_def]);
e(fs[perf_dist_sys_event_MS_def,series_MS_def,perf_dist_event_comp_def,GSPEC_OR,INTER_COMM,UNION_OVER_INTER]);
val PHI_COMP_CDFS=top_thm();

g`!X p j. ~NULL (X) ==> ((perf_dist_sys_event_MS parallel_MS X p j) = (BIGINTER(set (MAP (\a.(perf_dist_event_comp a p j)) X)))) `;
e(Induct_on`X` THEN rw[]);
e(Cases_on`X`);
e(fs[perf_dist_sys_event_MS_def,parallel_MS_def,perf_dist_event_comp_def]);
e(FIRST_X_ASSUM (MP_TAC o Q.SPECL [`p`,`j`]));
e(rw[EQ_SYM_EQ,perf_dist_sys_event_MS_def,parallel_MS_def]);
e(rw[INTER_DEF,perf_dist_event_comp_def,GSPEC_ETA]);
e(metis_tac[]);
val PHI_COMP_CDFS_p=top_thm();


g`!h L p j. ((perf_dist_sys_event_MS series_MS (X_list (h::L)) p j) = (BIGUNION(set (MAP (\a.(perf_dist_event_comp a p j)) (X_list (h::L))))))`;
e(rw[]);
e(MATCH_MP_TAC PHI_COMP_CDFS);
e(fs[X_list_def]);
val X_list_CDFs=top_thm();

g`!h L p j. ((perf_dist_sys_event_MS series_MS (Y_list (h::L)) p j) = (BIGUNION(set (MAP (\a.(perf_dist_event_comp a p j)) (Y_list (h::L))))))`;
e(rw[]);
e(MATCH_MP_TAC PHI_COMP_CDFS);
e(fs[Y_list_def]);
val Y_list_CDFs=top_thm();

g`! A B C.  A SUBSET B ==> A SUBSET (B UNION C)`;
e(fs[SUBSET_DEF, UNION_DEF]);
val SUBSET_UNION_TRANS=top_thm();
g`! A B C.  (A UNION (B UNION C)) = (B UNION (A UNION C))`;
e(REPEAT(GEN_TAC));
e(fs[UNION_DEF,GSPEC_ETA]);
e(rw[]);
e(ONCE_REWRITE_TAC[DISJ_COMM] THEN metis_tac[]);
val UNION3_COMM=top_thm();
(********* THM4a2 *******)
g`!L j p. ~NULL(L) /\ (prob_space p) /\
(!l. MEM l L ==> ((perf_dist_event_comp (FST l) p j) IN events p)) /\
 (!l. MEM l L ==> ((perf_dist_event_comp (SND l) p j) IN events p)) /\
 (!l. MEM l L ==> ((perf_dist_event_comp (FST l) p j) SUBSET (perf_dist_event_comp (SND l) p j)))
 ==> ((perf_dist_sys_MS series_MS (X_list L) p j) <= (perf_dist_sys_MS series_MS (Y_list L) p j))`;
e(fs[perf_dist_sys_MS_def]);
e(rw[]);
e(MATCH_MP_TAC PROB_INCREASING); 
e(Induct_on`L`);
e(fs[perf_dist_sys_event_MS_def,perf_dist_event_comp_def]);
e(fs[FORALL_AND_THM,DISJ_IMP_THM]);
e(rw[X_list_CDFs,Y_list_CDFs]);
e(Cases_on`L`);
e(fs[X_list_def,Y_list_def,perf_dist_sys_event_MS_def,perf_dist_event_comp_def]);
e(fs[X_list_def,Y_list_def,perf_dist_sys_event_MS_def,perf_dist_event_comp_def,X_list_CDFs,Y_list_CDFs]);
e(fs[FORALL_AND_THM,DISJ_IMP_THM]);
e(MATCH_MP_TAC EVENTS_UNION);
e(fs[]);
e(Cases_on`L`);
e(fs[X_list_def,Y_list_def,perf_dist_sys_event_MS_def,perf_dist_event_comp_def]);
e(fs[X_list_def,Y_list_def,perf_dist_sys_event_MS_def,perf_dist_event_comp_def,X_list_CDFs,Y_list_CDFs]);
e(fs[FORALL_AND_THM,DISJ_IMP_THM]);
e(MATCH_MP_TAC EVENTS_UNION);
e(fs[]);
e(Cases_on`L`);
e(fs[X_list_def,Y_list_def,perf_dist_sys_event_MS_def,perf_dist_event_comp_def]);
e(fs[X_list_CDFs,Y_list_CDFs,FORALL_AND_THM,DISJ_IMP_THM,X_list_def,Y_list_def]);
e(rw[]);
e(fs[SUBSET_UNION_TRANS]);
e(ONCE_REWRITE_TAC[UNION3_COMM] THEN fs[SUBSET_UNION_TRANS]);
e(ONCE_REWRITE_TAC[UNION_COMM] THEN fs[SUBSET_UNION_TRANS]);

(************** LEMMAS & DEFINITIONS : MUTUAL_INDEP ***************)
val list_prob_def = Define
    		 ` (list_prob p [] = []) /\
		 (!h t.list_prob p (h::t) =  prob p (h) :: list_prob p t )`;
val list_prod_def =  Define
 `(list_prod ([]) =  1:real ) /\
   		   (!h t . list_prod (h :: t)  =   (h:real) * (list_prod t ))`;

val inter_list_def =  Define
 ` (inter_list p ([]) = (p_space p  )) /\ 
 	  (!h t . inter_list p (h ::t)  = ( (h)  INTER (inter_list p t )))`;

val compl_list_def =  Define
` compl_list p L = MAP (\a. p_space p DIFF a) L`;

val mutual_indep_def = Define
 ` mutual_indep p (L) = !L1 n. (PERM L L1 /\ (1 <=  n /\ n <=  LENGTH(L)) ==> 
(  prob p (inter_list p (TAKE n L1)) = list_prod (list_prob p (TAKE n L1 ))))`;

(* ------------------------------------------------------------------------- *)
(*                 PERM_refl               *)
(* ------------------------------------------------------------------------- *)
val PERM_refl = Q.store_thm
("PERM_refl",
    `!L. PERM L L`,
    PROVE_TAC[PERM_DEF]);
(* ------------------------------------------------------------------------- *)
(*                 NULL_LENGTH_GE_ONE               *)
(* ------------------------------------------------------------------------- *)
g` !L. (~NULL(L)) <=>   (1 <=  LENGTH(L)) `;
e(Cases_on`L` THEN fs[]);
val NULL_LENGTH_GE_ONE=top_thm();

(* ------------------------------------------------------------------------- *)
(*                 MUTUAL_SUB_INDEP               *)
(* ------------------------------------------------------------------------- *)
g `!p L.  (~NULL(L)) /\ mutual_indep p L  ==> (prob p (inter_list p (TAKE (LENGTH(L) ) L )) =
        list_prod (list_prob p (TAKE (LENGTH(L)) L)))`;
e(rw[mutual_indep_def]);
e(FIRST_X_ASSUM (MP_TAC o Q.SPECL [`L`,`LENGTH((L:('a -> bool) list))`]));
e(fs[NULL_LENGTH_GE_ONE]);
val MUTUAL_SUB_INDEP = top_thm();
drop();
(* ------------------------------------------------------------------------- *)
(*                 LIST_INDEP               *)
(* ------------------------------------------------------------------------- *)
g `!p L.  (~NULL(L)) /\ mutual_indep p L  ==> ((prob p (inter_list p L)) =
        list_prod (list_prob p L))`;
e (rw[]);
e (KNOW_TAC (--` (L:('a -> bool) list) = (TAKE (LENGTH(L)) L )  `--));
e (fs[TAKE_LENGTH_ID ]);
e (DISCH_TAC);
e (ONCE_ASM_REWRITE_TAC[]);
e (MATCH_MP_TAC MUTUAL_SUB_INDEP);
e (fs[]);
val LIST_INDEP =  top_thm();
drop();
(* ------------------------------------------------------------------------- *)
(*                    MUTUAL_INDEP_TEMP1   *)
(* ------------------------------------------------------------------------- *)

g `!L1 L2 h.  mutual_indep p (h::L1 ++ L2) ==>  mutual_indep p (L1 ++ h::L2)`;
e (RW_TAC std_ss[mutual_indep_def]);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM (MP_TAC o Q.SPEC `(L1'):('a -> bool)list`));
e (RW_TAC std_ss[]);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM (MP_TAC o Q.SPEC `( n:num)`));
e (RW_TAC std_ss[]);
e (FULL_SIMP_TAC std_ss[]);
e (KNOW_TAC (--`PERM (h::L1 ++ L2) ((L1'):('a -> bool)list)`--));
e (MATCH_MP_TAC PERM_TRANS);
e (EXISTS_TAC(--`(((L1):('a -> bool)list) ++ h::L2)`--));
e (RW_TAC std_ss[]);
e (RW_TAC std_ss[PERM_EQUIVALENCE_ALT_DEF]);
e (MATCH_MP_TAC EQ_SYM);
e (RW_TAC std_ss[PERM_FUN_APPEND_CONS]);
e (RW_TAC std_ss[]);
e (FULL_SIMP_TAC std_ss[]);
e (KNOW_TAC (--` n <= LENGTH (h::((L1):('a -> bool)list) ++ L2)`--));
e (FULL_SIMP_TAC std_ss[LENGTH_APPEND]);
e (FULL_SIMP_TAC real_ss[LENGTH]);
e (RW_TAC std_ss[]);
val MUTUAL_INDEP_TEMP1 = top_thm();
drop();
(* ------------------------------------------------------------------------- *)
(*                    MUTUAL_INDEP_TEMP2   *)
(* ------------------------------------------------------------------------- *)
g `!L h. mutual_indep p (h::L) ==> mutual_indep p L`;
e (RW_TAC std_ss[mutual_indep_def]);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM (MP_TAC o Q.SPEC `(L1 ++ [h]):('a -> bool)list`));
e (RW_TAC std_ss[]);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM (MP_TAC o Q.SPEC `( n:num)`));
e (RW_TAC std_ss[]);
e (KNOW_TAC(--`(TAKE n ((L1 ++ [h]):('a -> bool)list)) =(TAKE n (L1)) `--));
e (MATCH_MP_TAC TAKE_APPEND1);
e (KNOW_TAC(--`LENGTH (L1:('a -> bool)list) = LENGTH ((L):('a -> bool)list) `--));
e (MATCH_MP_TAC PERM_LENGTH);
e (ONCE_REWRITE_TAC[PERM_SYM]);
e (RW_TAC std_ss[]);
e (DISCH_TAC);
e (ONCE_ASM_REWRITE_TAC[]);
e (RW_TAC std_ss[]);
e (DISCH_TAC);
e (FULL_SIMP_TAC std_ss[]);

e (KNOW_TAC(--` PERM (((h:('a -> bool))::L):('a -> bool)list) ((L1 ++ [h]):('a -> bool)list) /\ n <= LENGTH ((h::L):('a -> bool)list) `--));
e (RW_TAC std_ss[]);
e (KNOW_TAC(--` ((h::L):('a -> bool)list) =  [h ]++ (L:('a -> bool)list) `--));
e (RW_TAC list_ss[]);
e (DISCH_TAC);
e (ONCE_ASM_REWRITE_TAC[]);
e (MATCH_MP_TAC APPEND_PERM_SYM);
e (MATCH_MP_TAC PERM_CONG);
e (RW_TAC list_ss[PERM_REFL]);
e (MATCH_MP_TAC LESS_EQ_TRANS);
e (EXISTS_TAC(--`LENGTH (L:('a -> bool)list)`--));
e (RW_TAC list_ss[LENGTH]);
e (DISCH_TAC);
e (FULL_SIMP_TAC std_ss[]);
val MUTUAL_INDEP_TEMP2 = top_thm();
drop();
(* ------------------------------------------------------------------------- *)
(*                    MUTUAL_INDEP_TEMP5   *)
(* ------------------------------------------------------------------------- *)
g `!L1 L2 Q h.  mutual_indep p (h::L1 ++ Q::L2) ==>  mutual_indep p (L1 ++ Q::h::L2)`;
e (RW_TAC std_ss[mutual_indep_def]);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM (MP_TAC o Q.SPEC `(L1'):('a -> bool)list`));
e (RW_TAC std_ss[]);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM (MP_TAC o Q.SPEC `( n:num)`));
e (RW_TAC std_ss[]);
e (FULL_SIMP_TAC std_ss[]);
e (KNOW_TAC (--`PERM (h::L1 ++ Q::L2) ((L1'):('a -> bool)list)`--));
e (MATCH_MP_TAC PERM_TRANS);

e (EXISTS_TAC(--`(((L1):('a -> bool)list) ++ Q::h::L2)`--));
e (RW_TAC std_ss[]);
e (RW_TAC std_ss[PERM_EQUIVALENCE_ALT_DEF]);
e (MATCH_MP_TAC EQ_SYM);
e (RW_TAC std_ss[PERM_FUN_APPEND_CONS]);
e (RW_TAC std_ss[APPEND]);
e (RW_TAC std_ss[PERM_FUN_SWAP_AT_FRONT]);
e (RW_TAC std_ss[]);

e (FULL_SIMP_TAC std_ss[]);
e (KNOW_TAC (--` n <= LENGTH (h::((L1):('a -> bool)list) ++ Q::L2)`--));
e (FULL_SIMP_TAC std_ss[LENGTH_APPEND]);
e (FULL_SIMP_TAC real_ss[LENGTH]);
e (RW_TAC std_ss[]);
val MUTUAL_INDEP_TEMP5 = top_thm();
drop();
(* ------------------------------------------------------------------------- *)
(*                    MUTUAL_INDEP_TEMP6   *)
(* ------------------------------------------------------------------------- *)
g `!L1 L2 h.  mutual_indep p (h::L1) ==>  mutual_indep p (L1 ++ [h])`;
e (RW_TAC std_ss[mutual_indep_def]);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM (MP_TAC o Q.SPEC `(L1'):('a -> bool)list`));
e (RW_TAC std_ss[]);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM (MP_TAC o Q.SPEC `( n:num)`));
e (RW_TAC std_ss[]);
e (FULL_SIMP_TAC std_ss[]);
e (KNOW_TAC (--`PERM (h::L1) ((L1'):('a -> bool)list)`--));
e (MATCH_MP_TAC PERM_TRANS);
e (EXISTS_TAC(--`(((L1):('a -> bool)list) ++ [h])`--));
e (RW_TAC std_ss[]);
e (KNOW_TAC (--`((h::L1) :('a -> bool)list) = [h] ++ L1`--));
e (RW_TAC list_ss[]);
e (DISCH_TAC);
e (ONCE_ASM_REWRITE_TAC[]);
e (RW_TAC list_ss[PERM_APPEND]);
e (RW_TAC std_ss[]);
e (FULL_SIMP_TAC std_ss[]);
e (FULL_SIMP_TAC list_ss[LENGTH]);
val MUTUAL_INDEP_TEMP6 = top_thm();
drop();
(*******************)
g`!p j L. (MAP (λa. perf_dist_comp_MS a p j) L) = (list_prob p (MAP (λa. perf_dist_event_comp a p j) L))`;
e(Induct_on`L`);
e(rw[list_prob_def,perf_dist_comp_MS_def,perf_dist_event_comp_def]);
e(rw[perf_dist_comp_MS_def,list_prob_def]);
val list_prob_CDF_comp=top_thm();
drop();

g`!p j L. prob_space p ∧
  (!l. MEM l L ⇒ (perf_dist_event_comp l p j IN events p))   ==>
  ((MAP (λa. compl_perf_dist_comp_MS a p j) L) = (list_prob p (MAP (λa. ((p_space p) DIFF (perf_dist_event_comp a p j))) L)))`;
e(Induct_on`L`);
e(rw[list_prob_def,compl_perf_dist_comp_MS_def,perf_dist_event_comp_def]);
e(rw[compl_perf_dist_comp_MS_def,list_prob_def,PROB_COMPL,perf_dist_comp_MS_def]);
val list_prob_compl_CDF_comp=top_thm();
drop();
(*****************)
g`!L j p. ~NULL(L) /\ (prob_space p) /\
(!l. MEM l L ==> ((perf_dist_event_comp l p j) IN events p)) /\
(mutual_indep p (MAP (\a.(perf_dist_event_comp a p j)) L) )
 ==> ((list_prod (MAP (\a.(perf_dist_comp_MS a p j)) L)) <= (perf_dist_sys_MS series_MS L p j))`;
e(fs[PHI_COMP_CDFS,perf_dist_sys_MS_def,list_prob_CDF_comp]);
e(fs[NULL_LENGTH_GE_ONE,GSYM LIST_INDEP]);
e(rw[GSYM NULL_LENGTH_GE_ONE]);
e(MATCH_MP_TAC PROB_INCREASING); 
e(rw[]);
e(Induct_on`L`);
e(fs[]);
e(fs[FORALL_AND_THM,DISJ_IMP_THM]);
e(fs[inter_list_def]);
e(Cases_on`L`);
e(rw[inter_list_def,perf_dist_event_comp_def,INTER_COMM,INTER_ASSOC]);
e(ONCE_REWRITE_TAC[INTER_COMM]);
e(rw[]);
e(KNOW_TAC(--`mutual_indep p
        (perf_dist_event_comp h p j::MAP (λa. perf_dist_event_comp a p j) t)`--));
e(MATCH_MP_TAC MUTUAL_INDEP_TEMP2);
e (EXISTS_TAC(--`perf_dist_event_comp h' p j`--));
e(fs[]);
e(rw[]);
e(fs[FORALL_AND_THM,DISJ_IMP_THM,EVENTS_INTER]);
e(Induct_on`L`);
e(fs[]);
e(fs[FORALL_AND_THM,DISJ_IMP_THM]);
e(Cases_on`L`);
e(fs[]);
e(rw[]);
e(KNOW_TAC(--`mutual_indep p
        (perf_dist_event_comp h p j::MAP (λa. perf_dist_event_comp a p j) t)`--));
e(MATCH_MP_TAC MUTUAL_INDEP_TEMP2);
e (EXISTS_TAC(--`perf_dist_event_comp h' p j`--));
e(fs[]);
e(fs[FORALL_AND_THM,DISJ_IMP_THM,EVENTS_UNION]);
e(Induct_on`L`);
e(fs[]);
e(fs[FORALL_AND_THM,DISJ_IMP_THM]);
e(fs[inter_list_def]);
e(rw[]);
e(Cases_on`L`);
e(fs[inter_list_def]);
e(fs[]);
e(KNOW_TAC(--`mutual_indep p
        (perf_dist_event_comp h' p j::MAP (λa. perf_dist_event_comp a p j) t)`--));
e(MATCH_MP_TAC MUTUAL_INDEP_TEMP2);
e (EXISTS_TAC(--`perf_dist_event_comp h p j`--));
e(fs[]);
e(fs[SUBSET_DEF]);
val TH4i3s=top_thm();
(**************)
g`!p j L. ~NULL (L) ==> (inter_list p (MAP (λa. perf_dist_event_comp a p j) L) = BIGINTER (set (MAP (λa. perf_dist_event_comp a p j) L)))`;
e(Induct_on`L`);
e(fs[]);
e(rw[]); 
e(Cases_on`L`);
e(fs[inter_list_def,perf_dist_event_comp_def,GSYM INTER_ASSOC]);
e(fs[inter_list_def,perf_dist_event_comp_def,GSYM INTER_ASSOC]);
val list_BIG_INTER=top_thm();

g`!L j p. ~NULL(L) /\ (prob_space p) /\
(!l. MEM l L ==> ((perf_dist_event_comp l p j) IN events p)) /\
(mutual_indep p (MAP (\a.(perf_dist_event_comp a p j)) L) )
 ==> ((list_prod (MAP (\a.(perf_dist_comp_MS a p j)) L)) <= (perf_dist_sys_MS parallel_MS L p j))`;
e(fs[PHI_COMP_CDFS_p,perf_dist_sys_MS_def]);
e(fs[list_prob_CDF_comp]);
e(fs[NULL_LENGTH_GE_ONE,GSYM LIST_INDEP]);
e(fs[GSYM NULL_LENGTH_GE_ONE,list_BIG_INTER]);
val TH4i3p=top_thm();
(*************)
g`!A B D. A SUBSET B ⇒ D INTER A SUBSET D UNION B`;
e(fs[SUBSET_DEF]);
val SUBSET_INTER_UNION=top_thm();

g`!h h' L p. mutual_indep p (h::h'::L) ==> mutual_indep p (h'::h::L)`;
e(rw[mutual_indep_def]);
e(KNOW_TAC(--(`PERM (h'::h::L) (h:'a->bool::h'::L)`)--));
e(fs[PERM_SWAP_AT_FRONT]);
e(rw[]);
e(KNOW_TAC(--(`PERM (h:'a->bool::h'::L) L1`)--));
e(MATCH_MP_TAC PERM_TRANS);
e (EXISTS_TAC(--`(h'::h:'a->bool::L)`--));
e(fs[PERM_SYM]);
e(fs[]);
val mutual_cons_cons=top_thm();

drop();
g`!h h' L p. mutual_indep p (h::h'::L) <=> mutual_indep p (h'::h::L)`;
e(REPEAT(GEN_TAC) THEN EQ_TAC);
e(fs[mutual_cons_cons]);
e(fs[mutual_cons_cons]);
val mutual_cons_cons_eq=top_thm();
(*******)
g`!p L j h. (mutual_indep p ((perf_dist_event_comp h p j)::(MAP (λa. perf_dist_event_comp a p j) L))) ==> (mutual_indep p ((compl_list p [(perf_dist_event_comp h p j)])++(MAP (λa. perf_dist_event_comp a p j) L)))`;
e(fs[compl_list_def]);
e(rw[]);
e(KNOW_TAC(--`mutual_indep p
        (MAP (λa. perf_dist_event_comp a p j) L)`--));
e(MATCH_MP_TAC MUTUAL_INDEP_TEMP2);
e (EXISTS_TAC(--`perf_dist_event_comp h p j`--));
e(fs[]);
e(rw[]); 
e(Induct_on`L`);
e(fs[mutual_indep_def,list_prob_def,list_prod_def,inter_list_def,INTER_COMM,INTER_DEF,DIFF_DEF]);
e(fs[CONJ_ASSOC]);
e(rw[]);
(******* LEMMAS_mutual_indep ********)
g `!(L1:('a->bool) list) p . 
 prob_space p  /\ 
 (!x. MEM x (L1) ==> x IN events p ) ==> 
((L1:('a->bool) list) =  compl_list p (compl_list p L1)) `;
e(Induct_on`L1`);
e(fs[compl_list_def]);
e(fs[compl_list_def]);
e(rw[FORALL_AND_THM,DISJ_IMP_THM]);
e(KNOW_TAC(--` p_space p INTER h = h:'a->bool`--));
e(fs[INTER_PSPACE]);
e(rw[]);
e(MATCH_MP_TAC (GSYM DIFF_DIFF_SUBSET));
e(fs[INTER_SUBSET_EQN]);
val compl_compl_list=top_thm();
drop();

g`!L1' p. prob_space p /\ (∀x. MEM x L1' ⇒ x IN events p) ==> (∀x. MEM x (compl_list p L1') ⇒ x IN events p)`;
e(Induct_on`L1'`);
e(fs[compl_list_def]);
e(fs[FORALL_AND_THM,DISJ_IMP_THM,compl_list_def,EVENTS_COMPL]);
val events_compl_list=top_thm();
drop();
(*********************)
(*------------------MUTUAL_COMP_INDEP_THM_TEMP---------------------------*)
(* ------------------------------------------------------------------------- *)
(*                   TEMP_THM    *)
(* ------------------------------------------------------------------------- *)
g `!A C. COMPL A INTER C = C DIFF A INTER C`;
 e (SRW_TAC[][EXTENSION,IN_COMPL,IN_INTER]);
e (EQ_TAC);
e (RW_TAC std_ss[]);
e (RW_TAC std_ss[]);
val TEMP_THM =  top_thm();
drop();
(* ------------------------------------------------------------------------- *)
(*                   TEMP_THM_NEW    *)
(* ------------------------------------------------------------------------- *)
g `!A C. A INTER (p_space p DIFF C) = (A INTER p_space p DIFF (A INTER C))  `;
e (SRW_TAC[][EXTENSION,IN_COMPL,IN_INTER]);
e (EQ_TAC);
e (RW_TAC std_ss[]);
e (RW_TAC std_ss[]);
val TEMP_THM_NEW =  top_thm();
drop();
(* ------------------------------------------------------------------------- *)
(*                   TEMP_THM_NEW1    *)
(* ------------------------------------------------------------------------- *)
g `!A B C. A INTER B INTER C = (A INTER C) INTER B `;
e (SRW_TAC[][EXTENSION,IN_COMPL,IN_INTER]);
e (EQ_TAC);
e (RW_TAC std_ss[]);
e (RW_TAC std_ss[]);
val TEMP_THM_NEW1 =  top_thm();
drop();
 (* ------------------------------------------------------------------------- *)
(*                   TEMP_THM_NEW3    *)
(* ------------------------------------------------------------------------- *)
g `!A B C D. A INTER B INTER C INTER D = (B INTER C) INTER D INTER A `;
e (SRW_TAC[][EXTENSION,IN_COMPL,IN_INTER]);
e (EQ_TAC);
e (RW_TAC std_ss[]);
e (RW_TAC std_ss[]);
val TEMP_THM_NEW3 =  top_thm();
drop();
(* ------------------------------------------------------------------------- *)
(*                   TEMP_THM_NEW4    *)
(* ------------------------------------------------------------------------- *)
g `!A B C D. A INTER B INTER C INTER D = D INTER (A INTER B INTER C)`;
e (SRW_TAC[][EXTENSION,IN_COMPL,IN_INTER]);
e (EQ_TAC);
e (RW_TAC std_ss[]);
e (RW_TAC std_ss[]);
val TEMP_THM_NEW4 =  top_thm();
drop();
(*--------------------------------------------------------*)
(*----------------------INDEP_TEMP3----------------------------------*)
g `!m (L:('a->bool)list) x. MEM x (TAKE m L) ==> MEM x L `;
e (Induct);
e (Induct);
e (RW_TAC std_ss[TAKE_def,MEM]);
e (RW_TAC std_ss[TAKE_def,MEM]);
e (Induct);
e (RW_TAC std_ss[TAKE_def,MEM]);
e (RW_TAC list_ss[TAKE_def,MEM]);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM (MP_TAC o Q.SPEC `L`));
e (RW_TAC std_ss[]);
val INDEP_TEMP3 = top_thm();
drop();
(* ------------------------------------------------------------------------- *)
(*                   LEMMA7    *)
(* ------------------------------------------------------------------------- *)
g `!L p. (!x. MEM x L ==> x IN events p) /\
prob_space p ==> 
  (inter_list p L IN events p)`;
e (RW_TAC std_ss []);
e (Induct_on `L`);
  e (RW_TAC std_ss [MEM, inter_list_def,EVENTS_SPACE]);

  e (RW_TAC std_ss [MEM, inter_list_def]);

    	     e (MATCH_MP_TAC EVENTS_INTER);
	      e (RW_TAC std_ss []);
val LEMMA7 = top_thm();
drop();
(*----------------------PROB_COMPL_SUBSET--------------------------------*)
g`!p s t. prob_space p /\ s IN events p /\ t IN events p /\ t SUBSET s ==> (prob p (s DIFF t) = prob p s - prob p t)`;

e (METIS_TAC [MEASURE_COMPL_SUBSET,prob_space_def,events_def,prob_def,p_space_def]);

val PROB_COMPL_SUBSET = top_thm();
drop();
(*---------------------MUTUAL_INDEP_TEMP3_NEW-----------------------------*)
g `!L1 (L2:('a->bool)list) Q. (LENGTH (L1 ++ ((Q::L2))) = LENGTH ((Q::L1) ++ (L2)))`;
e (RW_TAC list_ss[LENGTH_APPEND]);
val MUTUAL_INDEP_TEMP3 = top_thm();
drop();

g `!L1 (L2:('a->bool)list) Q h. (LENGTH (L1 ++ ((Q::h::L2))) = LENGTH ((h::L1) ++ (Q::L2)))`;
e (RW_TAC list_ss[LENGTH_APPEND]);
val MUTUAL_INDEP_TEMP3_NEW = top_thm();
drop();
(*---------------------mutual_indep_lemma_new------------------------------------*)
g `!(L1:('a->bool) list) (L2:('a->bool) list) Q n p .prob_space p  /\ mutual_indep p (L1 ++ (Q::L2)) /\ (!x. MEM x (L1 ++ (Q::L2)) ==> x IN events p ) /\ 1 <=  (LENGTH (L1 ++ (Q::L2))) ==> (prob p (inter_list p (TAKE (n)(compl_list p L1) ) INTER  inter_list p ((Q::L2) )) =
        list_prod (list_prob p (TAKE (n)(compl_list p L1) )) * list_prod (list_prob p (( Q::L2) )))`;

e (Induct_on `L1`);
e (RW_TAC std_ss[compl_list_def,MAP]);
e (RW_TAC std_ss[TAKE_def]);
e (RW_TAC std_ss[inter_list_def,list_prob_def,list_prod_def]);
e (RW_TAC real_ss[]);
e (FULL_SIMP_TAC std_ss[mutual_indep_def]);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM (MP_TAC o Q.SPEC `((Q::L2):('a->bool)list)`));
e (RW_TAC real_ss[]);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM (MP_TAC o Q.SPEC `LENGTH ((Q::L2):('a->bool)list)`));
e (RW_TAC real_ss[]);
e (FULL_SIMP_TAC list_ss[PERM_REFL]);
e (FULL_SIMP_TAC list_ss[inter_list_def]);
e (KNOW_TAC (--`(p_space p INTER (Q INTER inter_list p ((L2:('a->bool)list)))) = (Q INTER inter_list p (L2))`--));
e (MATCH_MP_TAC INTER_PSPACE);
e (RW_TAC std_ss[]);
e (MATCH_MP_TAC EVENTS_INTER);
e (RW_TAC std_ss[]);
e (MATCH_MP_TAC LEMMA7);
e (RW_TAC std_ss[]);
e (DISCH_TAC);
e (ONCE_ASM_REWRITE_TAC[]);
e (RW_TAC std_ss[]);
e (RW_TAC std_ss[list_prob_def,list_prod_def]);


e (Induct_on `n`);
e (RW_TAC std_ss[compl_list_def,MAP]);
e (RW_TAC std_ss[TAKE_def]);
e (RW_TAC std_ss[inter_list_def,list_prob_def,list_prod_def]);

e (FULL_SIMP_TAC std_ss[APPEND]);
e (FULL_SIMP_TAC std_ss[LENGTH,LE_SUC]);
r(1);
e (FULL_SIMP_TAC std_ss[MUTUAL_INDEP_TEMP3]);
e (FULL_SIMP_TAC std_ss[APPEND]);
e (FULL_SIMP_TAC list_ss[LENGTH,LENGTH_NIL]);

e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM (MP_TAC o Q.SPEC `L2:('a->bool)list`));
e (RW_TAC real_ss[]);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM (MP_TAC o Q.SPEC `Q:('a->bool)`));
e (RW_TAC real_ss[]);

e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM (MP_TAC o Q.SPEC `0:num`));
e (RW_TAC real_ss[]);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM (MP_TAC o Q.SPEC `p:(  'a   -> bool) # ((  'a   -> bool) -> bool) # ((  'a   -> bool) -> real)`));
e (RW_TAC real_ss[]);
e (FULL_SIMP_TAC std_ss[]);
e (KNOW_TAC (--`mutual_indep p (L1 ++ ((Q::L2):('a->bool)list))`--));
e (MATCH_MP_TAC MUTUAL_INDEP_TEMP2);
e (RW_TAC std_ss[]);
e (EXISTS_TAC (--`h:'a->bool`--));
e (FULL_SIMP_TAC std_ss[APPEND]);
e (RW_TAC std_ss[]);
e (FULL_SIMP_TAC std_ss[]);
e (KNOW_TAC (--`(!x. MEM x ((L1:('a->bool) list) ++ Q::L2)==> x  IN  events p)`--));
e (RW_TAC std_ss[]);
e (FULL_SIMP_TAC list_ss[MEM]);
e (RW_TAC std_ss[]);
e (FULL_SIMP_TAC std_ss[]);
e (FULL_SIMP_TAC list_ss[TAKE_def,inter_list_def]);
e (RW_TAC std_ss[list_prob_def,list_prod_def]);
e (REAL_ARITH_TAC);
e (RW_TAC std_ss[compl_list_def,MAP,TAKE_def,HD,TL,inter_list_def]);
e (RW_TAC std_ss[INTER_ASSOC]);
e (ONCE_REWRITE_TAC[TEMP_THM_NEW3]);
e (RW_TAC std_ss[TEMP_THM_NEW]);
e (RW_TAC std_ss[GSYM compl_list_def]);
e (KNOW_TAC (--`prob p
  (inter_list p (TAKE n (compl_list p (L1:('a->bool) list))) INTER  Q INTER   inter_list p (L2:('a->bool) list) INTER 
   p_space p DIFF
   inter_list p (TAKE n (compl_list p L1)) INTER  (Q:('a->bool)) INTER  inter_list p L2 INTER   h) = prob p
  (inter_list p (TAKE n (compl_list p L1)) INTER  Q INTER   inter_list p L2 INTER  
   p_space p) -  prob p
   (inter_list p (TAKE n (compl_list p L1)) INTER  Q INTER   inter_list p L2 INTER   h) `--));


e (MATCH_MP_TAC PROB_COMPL_SUBSET);
e (RW_TAC std_ss[]);

e (MATCH_MP_TAC EVENTS_INTER);
e (RW_TAC std_ss[]);
e (MATCH_MP_TAC EVENTS_INTER);
e (RW_TAC std_ss[]);
e (MATCH_MP_TAC EVENTS_INTER);
e (RW_TAC std_ss[]);
e (MATCH_MP_TAC LEMMA7);
e (RW_TAC std_ss[]);
e (FULL_SIMP_TAC std_ss[]);
e (KNOW_TAC (--`(MEM x (compl_list p L1))`--));
e (MATCH_MP_TAC INDEP_TEMP3);
e (EXISTS_TAC (--`n:num`--));
e (RW_TAC std_ss[]);
e (DISCH_TAC);
e (FULL_SIMP_TAC std_ss[compl_list_def,MEM_MAP]);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM (MP_TAC o Q.SPEC `a`));
e (RW_TAC list_ss[MEM]);
e (FULL_SIMP_TAC std_ss[]);
e (MATCH_MP_TAC EVENTS_COMPL);
e (RW_TAC std_ss[]);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM (MP_TAC o Q.SPEC `Q`));
e (RW_TAC std_ss[]);
e (FULL_SIMP_TAC list_ss[MEM]);
e (MATCH_MP_TAC LEMMA7);
e (RW_TAC std_ss[]);
e (FULL_SIMP_TAC std_ss[]);
e (FULL_SIMP_TAC list_ss[MEM]);
e (MATCH_MP_TAC EVENTS_SPACE);
e (RW_TAC std_ss[]);
e (MATCH_MP_TAC EVENTS_INTER);
e (RW_TAC std_ss[]);

e (MATCH_MP_TAC EVENTS_INTER);
e (RW_TAC std_ss[]);
e (MATCH_MP_TAC EVENTS_INTER);
e (RW_TAC std_ss[]);
e (MATCH_MP_TAC LEMMA7);
e (RW_TAC std_ss[]);
e (FULL_SIMP_TAC std_ss[]);
e (KNOW_TAC (--`(MEM x (compl_list p L1))`--));
e (MATCH_MP_TAC INDEP_TEMP3);
e (EXISTS_TAC (--`n:num`--));
e (RW_TAC std_ss[]);
e (DISCH_TAC);
e (FULL_SIMP_TAC std_ss[compl_list_def,MEM_MAP]);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM (MP_TAC o Q.SPEC `a`));
e (RW_TAC list_ss[MEM]);
e (FULL_SIMP_TAC std_ss[]);
e (MATCH_MP_TAC EVENTS_COMPL);
e (RW_TAC std_ss[]);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM (MP_TAC o Q.SPEC `Q`));
e (RW_TAC std_ss[]);
e (FULL_SIMP_TAC list_ss[MEM]);

e (MATCH_MP_TAC LEMMA7);
e (RW_TAC std_ss[]);
e (FULL_SIMP_TAC std_ss[]);
e (FULL_SIMP_TAC list_ss[MEM]);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM (MP_TAC o Q.SPEC `h`));
e (RW_TAC std_ss[]);
e (FULL_SIMP_TAC list_ss[MEM]);

e (KNOW_TAC (--`inter_list p (TAKE n (compl_list p (L1:('a->bool) list))) INTER  Q INTER   inter_list p (L2:('a->bool) list) INTER  p_space p = inter_list p (TAKE n (compl_list p L1)) INTER  (Q:('a->bool)) INTER  inter_list p L2  `--));
e (ONCE_REWRITE_TAC[TEMP_THM_NEW4]);
e (MATCH_MP_TAC INTER_PSPACE);
e (RW_TAC std_ss[]);
e (MATCH_MP_TAC EVENTS_INTER);
e (RW_TAC std_ss[]);
e (MATCH_MP_TAC EVENTS_INTER);
e (RW_TAC std_ss[]);
e (MATCH_MP_TAC LEMMA7);
e (RW_TAC std_ss[]);
e (FULL_SIMP_TAC std_ss[]);
e (KNOW_TAC (--`(MEM x (compl_list p L1))`--));
e (MATCH_MP_TAC INDEP_TEMP3);
e (EXISTS_TAC (--`n:num`--));
e (RW_TAC std_ss[]);
e (DISCH_TAC);
e (FULL_SIMP_TAC std_ss[compl_list_def,MEM_MAP]);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM (MP_TAC o Q.SPEC `a`));
e (RW_TAC list_ss[MEM]);
e (FULL_SIMP_TAC std_ss[]);
e (MATCH_MP_TAC EVENTS_COMPL);
e (RW_TAC std_ss[]);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM (MP_TAC o Q.SPEC `Q`));
e (RW_TAC std_ss[]);
e (FULL_SIMP_TAC list_ss[MEM]);
e (MATCH_MP_TAC LEMMA7);
e (RW_TAC std_ss[]);
e (FULL_SIMP_TAC std_ss[]);
e (FULL_SIMP_TAC list_ss[MEM]);
e (DISCH_TAC);
e (ONCE_ASM_REWRITE_TAC[]);
e (RW_TAC std_ss[INTER_SUBSET]);
e (DISCH_TAC);
e (ONCE_ASM_REWRITE_TAC[]);
e (WEAKEN_TAC is_eq);
e (KNOW_TAC (--`(prob p
           (inter_list p (TAKE n (compl_list p (L1:('a->bool) list))) INTER 
            inter_list p (Q::L2)) =
         list_prod (list_prob p (TAKE n (compl_list p L1))) *
         list_prod (list_prob p (Q::(L2:('a->bool) list))))  `--));
e (FULL_SIMP_TAC std_ss[APPEND]);
e (FULL_SIMP_TAC std_ss[LENGTH,LE_SUC]);
r(1);
e (FULL_SIMP_TAC std_ss[MUTUAL_INDEP_TEMP3]);
e (FULL_SIMP_TAC std_ss[APPEND]);
e (FULL_SIMP_TAC list_ss[LENGTH,LENGTH_NIL]);

e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);

e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM (MP_TAC o Q.SPEC `L2:('a->bool)list`));
e (RW_TAC std_ss[]);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);

e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM (MP_TAC o Q.SPEC `Q`));
e (RW_TAC std_ss[]);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);

e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM (MP_TAC o Q.SPEC `n:num`));
e (RW_TAC std_ss[]);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);

e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM (MP_TAC o Q.SPEC `p:(  'a   -> bool) # ((  'a   -> bool) -> bool) # ((  'a   -> bool) -> real)`));
e (RW_TAC real_ss[]);
e (FULL_SIMP_TAC std_ss[]);
e (KNOW_TAC (--`mutual_indep p (L1 ++ ((Q::L2):('a->bool)list))`--));
e (MATCH_MP_TAC MUTUAL_INDEP_TEMP2);
e (RW_TAC std_ss[]);
e (EXISTS_TAC (--`h:'a->bool`--));
e (FULL_SIMP_TAC std_ss[APPEND]);
e (RW_TAC std_ss[]);
e (FULL_SIMP_TAC std_ss[]);
e (KNOW_TAC (--`(!x. MEM x ((L1:('a->bool) list) ++ Q::L2)==> x  IN  events p)`--));
e (RW_TAC std_ss[]);
e (FULL_SIMP_TAC list_ss[MEM]);
e (RW_TAC std_ss[]);
e (FULL_SIMP_TAC std_ss[]);
e (DISCH_TAC);
e (ONCE_ASM_REWRITE_TAC[]);
e (KNOW_TAC (--` (inter_list p (TAKE n (compl_list p (L1:('a->bool) list))) INTER  (Q:('a->bool)) INTER  inter_list p (L2:('a->bool) list) INTER 
   p_space p) = (inter_list p (TAKE n (compl_list p L1)) INTER  inter_list p (Q::L2))`--));
e (FULL_SIMP_TAC std_ss[inter_list_def]);
e (KNOW_TAC (--` (inter_list p (TAKE n (compl_list p (L1:('a->bool) list))) INTER  (Q:('a->bool)) INTER  inter_list p (L2:('a->bool) list) INTER 
   p_space p)= (inter_list p (TAKE n (compl_list p (L1:('a->bool) list))) INTER  (Q:('a->bool)) INTER  inter_list p (L2:('a->bool) list))`--));

e (RW_TAC std_ss[TEMP_THM_NEW4]);
e (MATCH_MP_TAC INTER_PSPACE);
e (RW_TAC std_ss[]);

e (RW_TAC std_ss[]);
e (MATCH_MP_TAC EVENTS_INTER);
e (RW_TAC std_ss[]);
e (MATCH_MP_TAC EVENTS_INTER);
e (RW_TAC std_ss[]);
e (MATCH_MP_TAC LEMMA7);
e (RW_TAC std_ss[]);
e (FULL_SIMP_TAC std_ss[]);
e (KNOW_TAC (--`(MEM x (compl_list p L1))`--));
e (MATCH_MP_TAC INDEP_TEMP3);
e (EXISTS_TAC (--`n:num`--));
e (RW_TAC std_ss[]);
e (DISCH_TAC);
e (FULL_SIMP_TAC std_ss[compl_list_def,MEM_MAP]);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM (MP_TAC o Q.SPEC `a`));
e (RW_TAC list_ss[MEM]);
e (FULL_SIMP_TAC std_ss[]);
e (MATCH_MP_TAC EVENTS_COMPL);
e (RW_TAC std_ss[]);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM (MP_TAC o Q.SPEC `Q`));
e (RW_TAC std_ss[]);
e (FULL_SIMP_TAC list_ss[MEM]);
e (MATCH_MP_TAC LEMMA7);
e (RW_TAC std_ss[]);
e (FULL_SIMP_TAC std_ss[]);
e (FULL_SIMP_TAC list_ss[MEM]);
e (RW_TAC std_ss[GSYM INTER_ASSOC]);
e (FULL_SIMP_TAC std_ss[]);
e (RW_TAC std_ss[GSYM INTER_ASSOC]);
e (FULL_SIMP_TAC std_ss[]);
e (WEAKEN_TAC is_eq);
e (WEAKEN_TAC is_eq);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);

e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM (MP_TAC o Q.SPEC `h::L2:('a->bool)list`));
e (RW_TAC std_ss[]);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);

e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM (MP_TAC o Q.SPEC `Q`));
e (RW_TAC std_ss[]);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);

e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM (MP_TAC o Q.SPEC `n:num`));
e (RW_TAC std_ss[]);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);

e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM (MP_TAC o Q.SPEC `p:(  'a   -> bool) # ((  'a   -> bool) -> bool) # ((  'a   -> bool) -> real)`));
e (RW_TAC real_ss[]);
e (FULL_SIMP_TAC std_ss[]);
e (KNOW_TAC (--`mutual_indep p (L1 ++ Q::(h::L2:('a->bool)list))`--));
e (MATCH_MP_TAC MUTUAL_INDEP_TEMP5);
e (RW_TAC real_ss[]);
e (RW_TAC real_ss[]);
e (FULL_SIMP_TAC std_ss[]);
e (KNOW_TAC (--`(!x. MEM x ((L1:('a->bool) list) ++ Q::h::L2)==> x  IN  events p)`--));
e (RW_TAC std_ss[]);
e (FULL_SIMP_TAC list_ss[MEM]);
e (RW_TAC std_ss[]);
e (FULL_SIMP_TAC std_ss[]);
e (FULL_SIMP_TAC std_ss[MUTUAL_INDEP_TEMP3_NEW]);
e (KNOW_TAC (--`(inter_list p (TAKE n (compl_list p (L1:('a->bool) list))) INTER  (Q:('a->bool)) INTER  inter_list p (L2:('a->bool) list) INTER  h) = (inter_list p (TAKE n (compl_list p L1)) INTER 
         inter_list p (Q::h::L2))`--));
e (RW_TAC real_ss[inter_list_def]);
e (SRW_TAC[][IN_INTER,EXTENSION,GSPECIFICATION]);
e (EQ_TAC);
e (RW_TAC real_ss[]);
e (RW_TAC real_ss[]);
e (DISCH_TAC);
e (ONCE_ASM_REWRITE_TAC[]);
e (RW_TAC real_ss[INTER_ASSOC]);
e (RW_TAC real_ss[]);
e (RW_TAC std_ss[list_prob_def,list_prod_def]);
e (WEAKEN_TAC is_eq);
e (KNOW_TAC (--`prob p (p_space p DIFF h)  = (1 - prob p (h:('a->bool)))`--));
e (MATCH_MP_TAC PROB_COMPL);
e (RW_TAC real_ss[]);
e (POP_ASSUM (MP_TAC o Q.SPEC `h`));
e (RW_TAC std_ss[]);
e (FULL_SIMP_TAC list_ss[MEM]);
e (DISCH_TAC);
e (ONCE_ASM_REWRITE_TAC[]);
e (REAL_ARITH_TAC);
val mutual_indep_lemma_new = top_thm();
drop();
(*-------------------mutual_compl_indep_lemma_new-------------------------------------*)
g `!(L1:('a->bool) list) n p . prob_space p  /\ mutual_indep p (L1) /\ (!x. MEM x (L1) ==> x IN events p ) /\ 1 <=  (LENGTH (L1)) ==> (prob p (inter_list p (TAKE (n)(compl_list p L1) )) =
        list_prod (list_prob p (TAKE (n)(compl_list p L1) )))`;
e (Induct_on `L1`);
e (RW_TAC std_ss[compl_list_def,MAP]);
e (RW_TAC list_ss[TAKE_def]);
e (RW_TAC std_ss[inter_list_def,list_prob_def,list_prod_def]);
e (RW_TAC real_ss[]);
e (FULL_SIMP_TAC list_ss[]);
e (RW_TAC real_ss[]);
e (FULL_SIMP_TAC list_ss[]);
e (FULL_SIMP_TAC list_ss[LE_SUC]);
r(1);
e (Induct_on `n`);
e (RW_TAC list_ss[TAKE_def]);
e (RW_TAC std_ss[inter_list_def,list_prob_def,list_prod_def,PROB_UNIV]);
e (RW_TAC std_ss[compl_list_def,MAP]);
e (RW_TAC list_ss[TAKE_def]);
e (RW_TAC std_ss[inter_list_def,list_prob_def,list_prod_def]);
e (RW_TAC real_ss[GSYM compl_list_def]);
e (ONCE_REWRITE_TAC [INTER_COMM]);
e (RW_TAC std_ss[TEMP_THM_NEW]);
e (RW_TAC std_ss[PROB_UNIV]);
e (KNOW_TAC (--`prob p
  (inter_list p (TAKE n (compl_list p (L1:('a->bool) list))) INTER  p_space p DIFF
   inter_list p (TAKE n (compl_list p L1)) INTER  (h:('a->bool)) ) = prob p
  (inter_list p (TAKE n (compl_list p L1)) INTER  p_space p ) - prob p (   inter_list p (TAKE n (compl_list p L1)) INTER  h)`--));

e (MATCH_MP_TAC PROB_COMPL_SUBSET);
e (RW_TAC std_ss[]);

e (MATCH_MP_TAC EVENTS_INTER);
e (RW_TAC std_ss[]);

e (MATCH_MP_TAC LEMMA7);
e (RW_TAC std_ss[]);
e (KNOW_TAC (--`(MEM x (compl_list p L1))`--));
e (MATCH_MP_TAC INDEP_TEMP3);
e (EXISTS_TAC (--`n:num`--));
e (RW_TAC std_ss[]);
e (DISCH_TAC);
e (FULL_SIMP_TAC std_ss[compl_list_def,MEM_MAP]);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM (MP_TAC o Q.SPEC `a`));
e (RW_TAC list_ss[MEM]);
e (FULL_SIMP_TAC std_ss[]);
e (MATCH_MP_TAC EVENTS_COMPL);
e (RW_TAC std_ss[]);
e (MATCH_MP_TAC EVENTS_SPACE);
e (RW_TAC std_ss[]);
e (MATCH_MP_TAC EVENTS_INTER);
e (RW_TAC std_ss[]);

e (MATCH_MP_TAC LEMMA7);
e (RW_TAC std_ss[]);
e (KNOW_TAC (--`(MEM x (compl_list p L1))`--));
e (MATCH_MP_TAC INDEP_TEMP3);
e (EXISTS_TAC (--`n:num`--));
e (RW_TAC std_ss[]);
e (DISCH_TAC);
e (FULL_SIMP_TAC std_ss[compl_list_def,MEM_MAP]);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM (MP_TAC o Q.SPEC `a`));
e (RW_TAC list_ss[MEM]);
e (FULL_SIMP_TAC std_ss[]);
e (MATCH_MP_TAC EVENTS_COMPL);
e (RW_TAC std_ss[]);
e (KNOW_TAC (--`inter_list p (TAKE n (compl_list p (L1:('a->bool) list))) INTER  p_space p = inter_list p (TAKE n (compl_list p L1))`--));
e (ONCE_REWRITE_TAC [INTER_COMM]);
e (MATCH_MP_TAC INTER_PSPACE);
e (RW_TAC std_ss[]);
e (MATCH_MP_TAC LEMMA7);
e (RW_TAC std_ss[]);
e (KNOW_TAC (--`(MEM x (compl_list p L1))`--));
e (MATCH_MP_TAC INDEP_TEMP3);
e (EXISTS_TAC (--`n:num`--));
e (RW_TAC std_ss[]);
e (DISCH_TAC);
e (FULL_SIMP_TAC std_ss[compl_list_def,MEM_MAP]);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM (MP_TAC o Q.SPEC `a`));
e (RW_TAC list_ss[MEM]);
e (FULL_SIMP_TAC std_ss[]);
e (MATCH_MP_TAC EVENTS_COMPL);
e (RW_TAC std_ss[]);
e (DISCH_TAC);
e (ONCE_ASM_REWRITE_TAC[]);
e (RW_TAC std_ss[INTER_SUBSET]);
e (FULL_SIMP_TAC list_ss[]);
e (DISCH_TAC);
e (ONCE_ASM_REWRITE_TAC[]);

e (WEAKEN_TAC is_eq); 
e (KNOW_TAC (--`inter_list p (TAKE n (compl_list p (L1:('a->bool) list))) INTER  p_space p = inter_list p (TAKE n (compl_list p L1))`--));
e (ONCE_REWRITE_TAC [INTER_COMM]);
e (MATCH_MP_TAC INTER_PSPACE);
e (RW_TAC std_ss[]);
e (MATCH_MP_TAC LEMMA7);
e (RW_TAC std_ss[]);
e (KNOW_TAC (--`(MEM x (compl_list p L1))`--));
e (MATCH_MP_TAC INDEP_TEMP3);
e (EXISTS_TAC (--`n:num`--));
e (RW_TAC std_ss[]);
e (DISCH_TAC);
e (FULL_SIMP_TAC std_ss[compl_list_def,MEM_MAP]);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM (MP_TAC o Q.SPEC `a`));
e (RW_TAC list_ss[MEM]);
e (FULL_SIMP_TAC std_ss[]);
e (MATCH_MP_TAC EVENTS_COMPL);
e (RW_TAC std_ss[]);
e (DISCH_TAC);
e (ONCE_ASM_REWRITE_TAC[]);
e (WEAKEN_TAC is_eq);
e (WEAKEN_TAC is_eq);

e (KNOW_TAC (--`(prob p (inter_list p (TAKE (n)(compl_list p L1) ) INTER  inter_list p ((h::[]) )) =
        list_prod (list_prob p (TAKE (n)(compl_list p L1) )) * list_prod (list_prob p ((( h::[]):('a->bool) list) )))`--));

e (MATCH_MP_TAC mutual_indep_lemma_new);
e (RW_TAC std_ss[]);
e (MATCH_MP_TAC MUTUAL_INDEP_TEMP6);
(*
e (EXISTS_TAC (--`(L1:('a->bool) list)`--));
*)
e (RW_TAC std_ss[]);
e (FULL_SIMP_TAC list_ss[MEM]);
e (FULL_SIMP_TAC list_ss[LENGTH]);
e (DISCH_TAC);
e (ONCE_ASM_REWRITE_TAC[]);
e (FULL_SIMP_TAC list_ss[inter_list_def]);
e (KNOW_TAC (--`(h INTER  p_space p) = (h:('a->bool))`--));
e (ONCE_REWRITE_TAC[INTER_COMM]);
e (MATCH_MP_TAC INTER_PSPACE);
e (RW_TAC std_ss[]);
e (RW_TAC std_ss[]);
e (FULL_SIMP_TAC std_ss[]);
e (WEAKEN_TAC is_eq);
e (WEAKEN_TAC is_eq);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM (MP_TAC o Q.SPEC `n:num`));
e (RW_TAC std_ss[]);

e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM (MP_TAC o Q.SPEC `p:(  'a   -> bool) # ((  'a   -> bool) -> bool) # ((  'a   -> bool) -> real)`));
e (RW_TAC std_ss[]);
e (FULL_SIMP_TAC std_ss[]);
e (Cases_on `L1`);
e (RW_TAC list_ss[compl_list_def,inter_list_def,list_prob_def,list_prod_def]);
e (RW_TAC real_ss[]);
e (FULL_SIMP_TAC list_ss[]);
e (RW_TAC std_ss[PROB_UNIV]);
e (RW_TAC std_ss[GSYM PROB_COMPL]);
e (FULL_SIMP_TAC list_ss[]);
e (KNOW_TAC (--` mutual_indep p ((h'::t):('a->bool)list)`--));
e (MATCH_MP_TAC  MUTUAL_INDEP_TEMP2);
e (EXISTS_TAC(--`h:'a->bool`--));
e (RW_TAC std_ss[]);
e (RW_TAC std_ss[]);
e (FULL_SIMP_TAC std_ss[]);
e (KNOW_TAC (--`prob p (p_space p DIFF h)  = (1 - prob p (h:('a->bool)))`--));
e (MATCH_MP_TAC PROB_COMPL);
e (RW_TAC real_ss[]);
e (RW_TAC std_ss[]);
e (FULL_SIMP_TAC list_ss[MEM]);
e (ONCE_ASM_REWRITE_TAC[]);
e (RW_TAC std_ss[list_prob_def,list_prod_def]);
e (REAL_ARITH_TAC);
val MUTUAL_COMP_INDEP_LEMMA_NEW = top_thm();
drop();
(*--------------*)
g `!(L1:('a->bool) list) p . prob_space p /\ mutual_indep p (compl_list p L1) /\ (!x. MEM x (L1) ==> x IN events p ) /\ 1 <=  (LENGTH (L1)) ==> mutual_indep p L1 `;
e (RW_TAC std_ss[]);
e (RW_TAC std_ss[mutual_indep_def]);
e (KNOW_TAC (--`(L1':('a->bool) list) =  compl_list p (compl_list p L1')`--));
e (MATCH_MP_TAC compl_compl_list);
e (fs[]);
e (KNOW_TAC (--`(!x. MEM x L1  =  MEM x (L1':('a->bool) list))`--));
e (MATCH_MP_TAC PERM_MEM_EQ);
e (fs[]);
e (fs[EQ_SYM_EQ]);
e (DISCH_TAC);
e (ONCE_ASM_REWRITE_TAC[]);
e (MATCH_MP_TAC  MUTUAL_COMP_INDEP_LEMMA_NEW);
e (RW_TAC std_ss[]);
e (FULL_SIMP_TAC list_ss[mutual_indep_def]);
e (RW_TAC std_ss[]);

e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM (MP_TAC o Q.SPEC `(L1'':('a->bool) list)`));
e (RW_TAC std_ss[]);

e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM MP_TAC);
e (POP_ASSUM (MP_TAC o Q.SPEC `n'`));
e (RW_TAC std_ss[]);
e (FULL_SIMP_TAC list_ss[]);
e (KNOW_TAC (--` PERM (compl_list p L1) (L1'':('a->bool) list)`--));
e (MATCH_MP_TAC PERM_TRANS);
e (EXISTS_TAC(--`(compl_list p L1')`--));
e (RW_TAC std_ss[]);
e (RW_TAC std_ss[compl_list_def]);
e (MATCH_MP_TAC PERM_MAP);
e (RW_TAC std_ss[]);
e (RW_TAC std_ss[]);
e (FULL_SIMP_TAC list_ss[]);
e (FULL_SIMP_TAC list_ss[compl_list_def,LENGTH_MAP]);
e (KNOW_TAC (--`LENGTH (L1:('a->bool) list) =  LENGTH (L1':('a->bool) list)`--));
e (MATCH_MP_TAC PERM_LENGTH);
e (RW_TAC std_ss[]);
e (RW_TAC std_ss[]);
e (FULL_SIMP_TAC list_ss[]);
e (KNOW_TAC (--`(!x. MEM x L1  =  MEM x (L1':('a->bool) list))`--));
e (MATCH_MP_TAC PERM_MEM_EQ);
e(fs[]);
e(rw[]);
e (KNOW_TAC (--`(!x'. MEM x' (compl_list p L1') ⇒ x' IN events p)`--));
e(MATCH_MP_TAC events_compl_list);
e(fs[]);
e(fs[compl_list_def]);
e(KNOW_TAC (--`LENGTH (L1:('a->bool) list) =  LENGTH (L1':('a->bool) list)`--));
e(MATCH_MP_TAC PERM_LENGTH);
e(rw[]);
e(fs[compl_list_def]);
val Mutual_indep_lemma2_new = top_thm();
drop();
(*********************)
g `!(L1:('a->bool) list) p . ~(NULL L1) /\ prob_space p /\ mutual_indep p (L1) /\ (!x. MEM x (L1) ==> x IN events p )  ==> mutual_indep p (compl_list p L1) `;
e(rw[]);
e(MATCH_MP_TAC Mutual_indep_lemma2_new);
e(rw[]);
e (KNOW_TAC (--`( compl_list p (compl_list p L1) = L1:('a->bool) list)`--));
e(MATCH_MP_TAC (GSYM compl_compl_list));
e(fs[]);
e(fs[]);
e (KNOW_TAC (--`!x. MEM x (compl_list p L1) ==> x IN events p`--));
e(MATCH_MP_TAC events_compl_list);
e(fs[]);
e(rw[]);
e(fs[NULL_LENGTH_GE_ONE,compl_list_def]);
val INDEP_COMPL_MUTUAL=top_thm();

(*********************) 

(***** THM 4.4 (i)******)
g`!L P. ~NULL (L) <=> ~NULL (MAP P L)`;
e(Induct_on`L` THEN fs[]);
val NULL_MAP=top_thm();
drop();
g`!L p j. prob_space p /\ (∀l. MEM l L ⇒ perf_dist_event_comp l p j IN events p) ==> (BIGUNION (set (MAP (λa. p_space p DIFF perf_dist_event_comp a p j) L)) IN events p)`;
e(Induct_on`L`);
e(fs[EVENTS_EMPTY]);
e(fs[FORALL_AND_THM,DISJ_IMP_THM]);
e(fs[EVENTS_UNION,EVENTS_COMPL]);
val EVENTS_UNION_COMPL_LIST=top_thm();
drop();
g`!L p j. prob_space p /\ (∀l. MEM l L ⇒ perf_dist_event_comp l p j IN events p) ==> (BIGUNION (set (MAP (λa. perf_dist_event_comp a p j) L)) IN events p)`;
e(Induct_on`L`);
e(fs[EVENTS_EMPTY]);
e(fs[FORALL_AND_THM,DISJ_IMP_THM]);
e(fs[EVENTS_UNION]);
val EVENTS_UNION_LIST=top_thm();
drop();

g`!L p j. prob_space p /\ (∀l. MEM l L ⇒ perf_dist_event_comp l p j IN events p) ==>( inter_list p
        (MAP (λa. p_space p DIFF perf_dist_event_comp a p j) L) IN
      events p)`;
e(Induct_on`L`);
e(rw[inter_list_def,EVENTS_SPACE]);
e(rw[inter_list_def,FORALL_AND_THM,DISJ_IMP_THM,EVENTS_INTER]);
e(MATCH_MP_TAC EVENTS_INTER);
e(fs[EVENTS_COMPL]);
val EVENTS_INTER_COMPL_LIST=top_thm();
drop();
g`!L p j. prob_space p /\ (∀l. MEM l L ⇒ perf_dist_event_comp l p j IN events p) ==>( inter_list p
        (MAP (λa. perf_dist_event_comp a p j) L) IN
      events p)`;
e(Induct_on`L`);
e(rw[inter_list_def,EVENTS_SPACE]);
e(rw[inter_list_def,FORALL_AND_THM,DISJ_IMP_THM,EVENTS_INTER]);
val EVENTS_INTER_LIST=top_thm();
drop();
g`!p P S L. mutual_indep p (P::MAP (S) L) ==> mutual_indep p (MAP (S) L)`;
e(rw[]);
e(MATCH_MP_TAC MUTUAL_INDEP_TEMP2);
e(EXISTS_TAC(--`P:'a->bool`--));
e(fs[]);
val MUTUAL_MAP_SUB_INDEP=top_thm();
drop();
g`!A B C. A INTER (B INTER C) = (A INTER C) INTER B`;
e (SRW_TAC[][IN_INTER,EXTENSION,GSPECIFICATION]);
e(metis_tac[]);
val ABC_ACB_INTER=top_thm();
drop();

g`!L j p. ~NULL(L) /\ (prob_space p) /\
(!l. MEM l L ==> ((perf_dist_event_comp l p j) IN events p)) /\
(mutual_indep p (MAP (\a.(perf_dist_event_comp a p j)) L) )
 ==>( (perf_dist_sys_MS series_MS L p j) <= (1-(list_prod (MAP (\a.(compl_perf_dist_comp_MS a p j)) L))))`;
e(rw[PHI_COMP_CDFS,perf_dist_sys_MS_def,list_prob_compl_CDF_comp]);
e(KNOW_TAC(--`mutual_indep p ( compl_list p
        (MAP (λa. perf_dist_event_comp a p j) L))`--));
e(MATCH_MP_TAC INDEP_COMPL_MUTUAL);
e(fs[MEM_MAP]);
e(rw[]);
e(Induct_on`L` THEN fs[]);
e(FIRST_X_ASSUM (MP_TAC o Q.SPECL [`a`]) THEN fs[]);
e(fs[compl_list_def,GSYM LIST_INDEP]);
e(fs[MAP_MAP_o,o_DEF]);
e(KNOW_TAC(--`~NULL((MAP (λa. p_space p DIFF perf_dist_event_comp a p j) L))`--));
e(fs[GSYM NULL_MAP]);
e(fs[GSYM NULL_MAP, GSYM LIST_INDEP]);
e(fs[EVENTS_INTER_COMPL_LIST,GSYM PROB_COMPL]);
e(rw[]);
e(MATCH_MP_TAC PROB_INCREASING);
e(rw[EVENTS_DIFF,EVENTS_UNION_LIST,EVENTS_INTER_COMPL_LIST,EVENTS_SPACE]);
e(fs[SUBSET_DIFF]);
e(rw[]);
e(Induct_on`L`);
e(fs[]);
e(fs[FORALL_AND_THM,DISJ_IMP_THM]);
e(rw[perf_dist_event_comp_def]);
e(fs[GSYM perf_dist_event_comp_def]);
e(KNOW_TAC(--`mutual_indep p
        (MAP (λa. perf_dist_event_comp a p j) L)`--));
e(MATCH_MP_TAC MUTUAL_INDEP_TEMP2);
e (EXISTS_TAC(--`perf_dist_event_comp h p j`--));
e(fs[] THEN rw[] THEN fs[]);
e(KNOW_TAC(--`mutual_indep p
        (MAP (λa. p_space p DIFF perf_dist_event_comp a p j) L)`--));
e(MATCH_MP_TAC MUTUAL_INDEP_TEMP2);
e (EXISTS_TAC(--`p_space p DIFF perf_dist_event_comp h p j`--));
e(fs[] THEN rw[] THEN fs[]);
e(rw[] THEN fs[]);
e(Cases_on`L`);
e(fs[]);
e(fs[]);
e(Induct_on`L`);
e(fs[]);
e(fs[FORALL_AND_THM,DISJ_IMP_THM]);
e(rw[inter_list_def]); 
e(fs[DISJOINT_DEF]);
e(KNOW_TAC(--`mutual_indep p
        (MAP (λa. perf_dist_event_comp a p j) L)`--));
e(MATCH_MP_TAC MUTUAL_INDEP_TEMP2);
e (EXISTS_TAC(--`perf_dist_event_comp h p j`--));
e(fs[] THEN rw[] THEN fs[]);
e(KNOW_TAC(--`mutual_indep p
        (MAP (λa. p_space p DIFF perf_dist_event_comp a p j) L)`--));
e(MATCH_MP_TAC MUTUAL_INDEP_TEMP2);
e (EXISTS_TAC(--`p_space p DIFF perf_dist_event_comp h p j`--));
e(fs[] THEN rw[] THEN fs[]);
e(rw[] THEN fs[]);
e(Cases_on`L`);
e(fs[]);
e(fs[inter_list_def,perf_dist_event_comp_def]);
e (SRW_TAC[][IN_INTER,EXTENSION,GSPECIFICATION]);
e(metis_tac[]);
e (SRW_TAC[][IN_INTER,EXTENSION,GSPECIFICATION]);
e(metis_tac[]);
e(KNOW_TAC(--`mutual_indep p
        (MAP (λa. perf_dist_event_comp a p j) L)`--));
e(MATCH_MP_TAC MUTUAL_INDEP_TEMP2);
e (EXISTS_TAC(--`perf_dist_event_comp h p j`--));
e(fs[] THEN rw[] THEN fs[]);
e(KNOW_TAC(--`mutual_indep p
        (MAP (λa. p_space p DIFF perf_dist_event_comp a p j) L)`--));
e(MATCH_MP_TAC MUTUAL_INDEP_TEMP2);
e (EXISTS_TAC(--`p_space p DIFF perf_dist_event_comp h p j`--));
e(fs[] THEN rw[] THEN fs[]);
e(rw[] THEN fs[]);
e(Cases_on`L`);
e(fs[]);
e(fs[DISJOINT_DEF]);
e(fs[ABC_ACB_INTER]);
e(fs[ABC_ACB_INTER]);
val TH4iia=top_thm();

g`!L j p. ~NULL(L) /\ (prob_space p) /\
(!l. MEM l L ==> ((perf_dist_event_comp l p j) IN events p)) /\
(mutual_indep p (MAP (\a.(perf_dist_event_comp a p j)) L) )
 ==>( (perf_dist_sys_MS parallel_MS L p j) <= (1-(list_prod (MAP (\a.(compl_perf_dist_comp_MS a p j)) L))))`;

e(rw[PHI_COMP_CDFS_p,perf_dist_sys_MS_def,list_prob_compl_CDF_comp,GSYM list_BIG_INTER]);
e(KNOW_TAC(--`mutual_indep p ( compl_list p
        (MAP (λa. perf_dist_event_comp a p j) L))`--));
e(MATCH_MP_TAC INDEP_COMPL_MUTUAL);
e(fs[MEM_MAP]);
e(rw[]);
e(Induct_on`L` THEN fs[]);
e(FIRST_X_ASSUM (MP_TAC o Q.SPECL [`a`]) THEN fs[]);
e(fs[compl_list_def,GSYM LIST_INDEP]);
e(fs[MAP_MAP_o,o_DEF]);
e(KNOW_TAC(--`~NULL((MAP (λa. p_space p DIFF perf_dist_event_comp a p j) L))`--));
e(fs[GSYM NULL_MAP]);
e(fs[GSYM NULL_MAP, GSYM LIST_INDEP]);
e(fs[EVENTS_INTER_COMPL_LIST,GSYM PROB_COMPL]);
e(rw[]);
e(MATCH_MP_TAC PROB_INCREASING);
e(rw[EVENTS_DIFF,EVENTS_UNION_LIST,EVENTS_INTER_COMPL_LIST,EVENTS_INTER_LIST,EVENTS_SPACE]);
e(fs[SUBSET_DIFF]);
e(fs[GSYM INTER_SUBSET_EQN]);
e(fs[EVENTS_INTER_LIST,INTER_COMM,INTER_PSPACE]);
e(Induct_on`L`);
e(fs[]);
e(fs[FORALL_AND_THM,DISJ_IMP_THM]);
e(fs[]);
e(rw[]);
e(KNOW_TAC(--`mutual_indep p
        (MAP (λa. perf_dist_event_comp a p j) L)`--));
e(MATCH_MP_TAC MUTUAL_INDEP_TEMP2);
e (EXISTS_TAC(--`perf_dist_event_comp h p j`--));
e(fs[] THEN rw[] THEN fs[]);
e(KNOW_TAC(--`mutual_indep p
        (MAP (λa. p_space p DIFF perf_dist_event_comp a p j) L)`--));
e(MATCH_MP_TAC MUTUAL_INDEP_TEMP2);
e (EXISTS_TAC(--`p_space p DIFF perf_dist_event_comp h p j`--));
e(fs[] THEN rw[] THEN fs[]);
e(rw[] THEN fs[]);
e(Cases_on`L`);
e(fs[DISJOINT_DEF,perf_dist_event_comp_def,inter_list_def]);
e (SRW_TAC[][IN_INTER,EXTENSION,GSPECIFICATION]);
e(metis_tac[]);
e(fs[DISJOINT_DEF,perf_dist_event_comp_def,inter_list_def]);
e (SRW_TAC[][IN_INTER,EXTENSION,GSPECIFICATION]);
e(metis_tac[]);
val TH4iib=top_thm();
(*******************************************)
(*******************************************)
val perf_dist_seg_def= Define
`∀p s.
perf_dist_seg p s =
(perf_comp_MS (FST s) p (FST (SND s)) = (SND (SND s)))`;

val perf_dist_seg_list_def= Define
`(∀p.
perf_dist_seg_list p [] = T) ∧
(∀p h t.
perf_dist_seg_list p (h::t) =
perf_dist_seg p h ∧ perf_dist_seg_list p t)`;

val seg_tuple_list_def= Define
`∀p.
seg_tuple_list X L = MAP (λa. (X,a)) L`;

val comp_state_pred_def= Define
`∀p S SL.
comp_state_pred p (S:'a->num) (SL:(num#real) list) =
(perf_dist_seg_list p (seg_tuple_list S SL)) ∧
(comp_events_space S (LENGTH SL) = (p_space p))`;

val perf_pipeline_series_MS_def=Define
`∀L p j.
perf_pipeline_series_MS L p j =
prob p (perf_dist_sys_event_MS series_MS L p j)`;

val sum_list_def=Define
`(∀n. sum_list (n:num) [] = 0:real) ∧
(∀n x xs.
  sum_list n (x::xs) =
   if n = 0 then 0 else ((SND x) + sum_list (n-1) xs))`;


g`∀SL pSL j p. 
Let
val SL = [S1;S2;S3;S4;S5;S6;S7;S8;S9;S10]
 val pSL = [[p1_0;p1_1;p1_2;p1_3;p1_4]:num#real list;[p2_0;p2_1;p2_2;p2_3;p2_4];
           [p3_0;p3_1;p3_2;p3_3;p3_4];[p4_0;p4_1;p4_2;p4_3;p4_4];
           [p5_0;p5_1;p5_2;p5_3;p5_4];[p6_0;p6_1;p6_2;p6_3;p6_4];
           [p7_0;p7_1;p7_2;p7_3;p7_4];[p8_0;p8_1;p8_2;p8_3;p8_4];
           [p9_0;p9_1;p9_2;p9_3;p9_4];[p10_0;p10_1;p10_2;p10_3;p10_4]]
in
prob_space p ∧
(∀l. MEM l (ZIP(SL,pSL)) ⇒ (comp_state_pred p (FST l) (SND l))) ∧
(∀l. MEM l SL ⇒ (perf_dist_event_comp l p j ∈ events p)) ∧
mutual_indep p (MAP (λa. perf_dist_event_comp a p j) SL) ⇒
(perf_pipeline_series_MS SL p j =
1-((1-sum_list j [p1_0;p1_1;p1_2;p1_3;p1_4])*(1-sum_list j [p2_0;p2_1;p2_2;p2_3;p2_4])*
   (1-sum_list j [p3_0;p3_1;p3_2;p3_3;p3_4])*(1-sum_list j [p4_0;p4_1;p4_2;p4_3;p4_4])*
   (1-sum_list j [p5_0;p5_1;p5_2;p5_3;p5_4])*(1-sum_list j [p6_0;p6_1;p6_2;p6_3;p6_4])*
   (1-sum_list j [p7_0;p7_1;p7_2;p7_3;p7_4])*(1-sum_list j [p8_0;p8_1;p8_2;p8_3;p8_4])*
   (1-sum_list j [p9_0;p9_1;p9_2;p9_3;p9_4])*(1-sum_list j [p10_0;p10_1;p10_2;p10_3;p10_4])))`;

g`∀SL pSL j p. 
 (SL = [S1;S2;S3;S4;S5;S6;S7;S8;S9;S10]) /\  
 (pSL = [[p1_0;p1_1;p1_2;p1_3;p1_4];[p2_0;p2_1;p2_2;p2_3;p2_4];
           [p3_0;p3_1;p3_2;p3_3;p3_4];[p4_0;p4_1;p4_2;p4_3;p4_4];
           [p5_0;p5_1;p5_2;p5_3;p5_4];[p6_0;p6_1;p6_2;p6_3;p6_4];
           [p7_0;p7_1;p7_2;p7_3;p7_4];[p8_0;p8_1;p8_2;p8_3;p8_4];
           [p9_0;p9_1;p9_2;p9_3;p9_4];[p10_0;p10_1;p10_2;p10_3;p10_4]])
/\ prob_space p ∧
(∀l. MEM l (ZIP(SL,pSL)) ⇒ (comp_state_pred p (FST l) (SND l))) ∧
(∀l. MEM l SL ⇒ (perf_dist_event_comp l p j ∈ events p)) ∧
mutual_indep p (MAP (λa. perf_dist_event_comp a p j) SL) ⇒
(perf_pipeline_series_MS SL p j =
1-((1-sum_list j [p1_0;p1_1;p1_2;p1_3;p1_4])*(1-sum_list j [p2_0;p2_1;p2_2;p2_3;p2_4])*
   (1-sum_list j [p3_0;p3_1;p3_2;p3_3;p3_4])*(1-sum_list j [p4_0;p4_1;p4_2;p4_3;p4_4])*
   (1-sum_list j [p5_0;p5_1;p5_2;p5_3;p5_4])*(1-sum_list j [p6_0;p6_1;p6_2;p6_3;p6_4])*
   (1-sum_list j [p7_0;p7_1;p7_2;p7_3;p7_4])*(1-sum_list j [p8_0;p8_1;p8_2;p8_3;p8_4])*
   (1-sum_list j [p9_0;p9_1;p9_2;p9_3;p9_4])*(1-sum_list j [p10_0;p10_1;p10_2;p10_3;p10_4])))`;
   
   
