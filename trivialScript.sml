open HolKernel Parse boolLib bossLib;
open simpLib;
open monadsyntax
open markerTheory;
open combinTheory;
open pairTheory;
open arithmeticTheory;
open pred_setTheory;
open listTheory;
open rich_listTheory;
open finite_mapTheory;
open realTheory;
open realLib;
open limTheory;
open transcTheory;
open real_sigmaTheory;
open binary_ieeeTheory;
open extrealTheory;
open util_probTheory;
open sigma_algebraTheory;
open measureTheory;
open borelTheory;
open lebesgueTheory;
open martingaleTheory;
open probabilityTheory;

val _ = new_theory "trivial";

(* Voodoo definitions *)

val name_to_thname = fn s => ({Thy = "trival", Name = s}, DB.fetch "trivial" s);

val mk_local_simp = augment_srw_ss o single o rewrites_with_names o single o name_to_thname;

(* Toggles *)

val _ = reveal "C";

val _ = temp_enable_monadsyntax()

val _ = temp_enable_monad "option"

(*---------------------------------------------------------------------------*)
(* Offensively Trivial stuff (Combinとか, Pairとか) *)
(*---------------------------------------------------------------------------*)

Definition DUP_DEF:
    DUP x = (x,x)
End

Theorem Abbrev_T:
    Abbrev T = T
Proof
    rw[Abbrev_def]
QED

val _ = mk_local_simp "Abbrev_T";

Theorem FORALL_IMP_CONJ_THM:
    ∀P Q R. (∀x. P x ⇒ Q x ∧ R x) ⇔ (∀x. P x ⇒ Q x) ∧ (∀x. P x ⇒ R x)
Proof
    simp[IMP_CONJ_THM,FORALL_AND_THM]
QED

(*
I_EQ_IDABS
Theorem I_ALT:
    I = (λx. x)
Proof
    rw[FUN_EQ_THM]
QED
*)

Theorem C_SIMP:
    ∀P x y. C (λx y. P x y) y = (λx. P x y)
Proof
    rw[FUN_EQ_THM]
QED

Theorem C_C:
    ∀f x. C (C f) x = f x
Proof
    rw[FUN_EQ_THM]
QED

(*
ETA_AX
Theorem F_SIMP:
    ∀f. (λx. f x) = f
Proof
    rw[FUN_EQ_THM]
QED
*)

Theorem IRULER:
    ∀P x y. x = y ⇒ P x = P y
Proof
    rw[]
QED

Theorem AND_IMP_OR:
    ∀P Q. P ∧ Q ⇒ P ∨ Q
Proof
    simp[]
QED

Theorem ELIM_UNCURRY_PAIRARG:
    ∀f. UNCURRY f = (λ(x,y). f x y)
Proof
    simp[FUN_EQ_THM]
QED

Theorem PAIR_FUN2:
    ∀P xy. (λ(x,y). P x y) xy = P (FST xy) (SND xy)
Proof
    rw[] >> Cases_on `xy` >> simp[]
QED

Theorem PAIR_FUN3:
    ∀P xyz. (λ(x,y,z). P x y z) xyz = P (FST xyz) (FST (SND xyz)) (SND (SND xyz))
Proof
    rw[] >> Cases_on `xyz` >> simp[PAIR_FUN2]
QED

Theorem PAIR_FUN4:
    ∀P wxyz. (λ(w,x,y,z). P w x y z) wxyz =
        P (FST wxyz) (FST (SND wxyz)) (FST (SND (SND wxyz))) (SND (SND (SND wxyz)))
Proof
    rw[] >> Cases_on `wxyz` >> simp[PAIR_FUN3]
QED

(*
PAIR_FST_SND_EQ
Theorem PAIR_EQ_ALT:
    ∀x y. x = y ⇔ FST x = FST y ∧ SND x = SND y
Proof
    rw[] >> map_every (fn tm => (qspec_then tm assume_tac) ABS_PAIR_THM) [`x`,`y`] >> fs[]
QED
*)

(*---------------------------------------------------------------------------*)
(* Trivial stuff for Arithmetic *)
(*---------------------------------------------------------------------------*)

Theorem DIV_MOD_EQ:
    ∀x y z. 0 < z ⇒ ((x = y) ⇔ (x DIV z = y DIV z) ∧ (x MOD z = y MOD z))
Proof
    rw[] >> eq_tac >> fs[] >> rw[] >> imp_res_tac DA >>
    pop_assum (fn th => map_every (fn sp => (qspec_then sp assume_tac) th) [`x`,`y`]) >>
    fs[] >> rw[] >> Q.RENAME_TAC [`r + q * z = s + p * z`] >>
    (fn th => map_every (fn sp => (qspecl_then sp assume_tac) th) [[`z`,`r`],[`z`,`s`]]) DIV_MULT >>
    rfs[] >> fs[]
QED

Theorem LT_PROD_MOD_DIV:
    ∀m n k. k < m * n ⇒ k MOD m < m ∧ k DIV m < n
Proof
    rw[] >> `0 < m` by (CCONTR_TAC >> fs[])
    >- (rw[DIVISION])
    >- (drule_then assume_tac DA >> pop_assum (qspec_then `k` assume_tac) >>
        fs[] >> rw[] >> drule_then assume_tac DIV_MULT >> fs[] >>
        NTAC 2 (pop_assum kall_tac) >> CCONTR_TAC >> `n ≤ q` by fs[] >>
        `m * n ≤ m * q` by fs[] >>
        (qspecl_then [`0`,`m * n`,`r`,`m * q`] assume_tac) LESS_EQ_LESS_EQ_MONO >> rfs[])
QED

Theorem MOD_DIV_LT_PROD:
    ∀x:num y m n. x < m ∧ y < n ⇒ y * m + x < m * n
Proof
    rw[] >> `1 + y ≤ n` by fs[] >> `m * (1 + y) ≤ n * m` by fs[] >> fs[LEFT_ADD_DISTRIB]
QED

Theorem ODD_POS:
    ∀n. ODD n ⇒ 0 < n
Proof
    rw[] >> Cases_on `n` >> fs[]
QED

(*
LESS_EQ_IFF_LESS_SUC
Theorem LE_LT_SUC:
    ∀x y. x ≤ y ⇔ x < SUC y
Proof
    rw[]
QED
*)

(*---------------------------------------------------------------------------*)
(* Trivial stuff for Pred Set *)
(*---------------------------------------------------------------------------*)

(*
UNIV_FUNSET_UNIV
Theorem UNIV_FUN:
    FUNSET 𝕌(:α) 𝕌(:β) = 𝕌(:α -> β)
Proof
    rw[EXTENSION,FUNSET]
QED
*)

Theorem BIJ_I:
    ∀s. I PERMUTES s
Proof
    rw[I_EQ_IDABS,BIJ_ID]
QED

Theorem EMPTY_KF:
    ∅ = K F
Proof
    rw[EXTENSION,IN_APP]
QED

Theorem PAIR_MAP_IMAGE_CROSS:
    ∀f g s t. IMAGE (f ## g) (s × t) = (IMAGE f s) × (IMAGE g t)
Proof
    rw[EXTENSION,PAIR_MAP] >> eq_tac >> rw[] >> fs[]
    >- (rename [`FST z ∈ s`] >> qexists_tac `FST z` >> rw[])
    >- (rename [`FST z ∈ s`] >> qexists_tac `SND z` >> rw[])
    >- (rename [`FST z = f x`,`SND z = g y`] >> qexists_tac `(x,y)` >> fs[] >>
        NTAC 2 (qpat_x_assum `_ = _` (fn th => rw[GSYM th])))
QED

Theorem PAIR_MAP_PREIMAGE_CROSS:
    ∀f g s t. PREIMAGE (f ## g) (s × t) = (PREIMAGE f s) × (PREIMAGE g t)
Proof
    rw[EXTENSION,PAIR_MAP] >> eq_tac >> rw[] >> fs[]
QED

Theorem BIJ_CROSS:
    ∀a b c d f g. BIJ f a b ∧ BIJ g c d ⇒ BIJ (f ## g) (a × c) (b × d)
Proof
    rw[BIJ_DEF,INJ_DEF,SURJ_DEF,PAIR_MAP]
    >- (NTAC 2 (qpat_x_assum `∀x y. _` (dxrule_all_then assume_tac)) >> rw[PAIR_FST_SND_EQ])
    >- (NTAC 2 (qpat_x_assum `∀x. _ ⇒ ∃y. _` (dxrule_then assume_tac)) >> fs[] >>
        rename [`f y0 = FST x`,`g y1 = SND x`] >> qexists_tac `(y0,y1)` >> fs[])
QED

(*
INTER_CROSS
Theorem CROSS_INTER:
    ∀a b c d. (a × b) ∩ (c × d) = (a ∩ c) × (b ∩ d)
Proof
    rw[EXTENSION] >> eq_tac >> rw[]
QED
*)

Theorem SET_DEMORGANS:
    ∀x y z. (x DIFF (y ∪ z) = (x DIFF y) ∩ (x DIFF z)) ∧ (x DIFF (y ∩ z) = (x DIFF y) ∪ (x DIFF z))
Proof
    rpt strip_tac >> fs[EXTENSION] >> strip_tac >> eq_tac >> rw[] >> fs[]
QED

Theorem DIFF_DIFF2:
    ∀s t. s DIFF (s DIFF t) = s ∩ t
Proof
    rw[EXTENSION] >> eq_tac >> rw[]
QED

Theorem UNION_INTER_DIFF:
    ∀s t. (s ∩ t) ∪ (s DIFF t) = s
Proof
    rw[EXTENSION] >> eq_tac >> rw[]
QED

Theorem DISJOINT_INTER_DIFF:
    ∀s t. DISJOINT (s ∩ t) (s DIFF t)
Proof
    simp[DISJOINT_ALT]
QED

Theorem BIJ_IMP_121C:
    ∀f s t x y. BIJ f s t ∧ x ∈ s ∧ y ∈ s ⇒ ((f x = f y) ⇔ (x = y))
Proof
    rw[BIJ_ALT,EXISTS_UNIQUE_DEF] >> eq_tac >> rw[] >> fs[FUNSET]
QED

Theorem BIJ_IMAGE_PREIMAGE:
    ∀f s a b. BIJ f a b ∧ s ⊆ b ⇒ (IMAGE f (PREIMAGE f s ∩ a) = s)
Proof
    rw[] >> irule SUBSET_ANTISYM >> rw[IMAGE_PREIMAGE] >> rw[SUBSET_DEF] >>
    fs[PREIMAGE_def] >> `x ∈ b` by fs[SUBSET_DEF] >> fs[BIJ_ALT] >> RES_TAC >>
    fs[EXISTS_UNIQUE_THM] >> qexists_tac `x'` >> rw[]
QED

Theorem BIJ_PREIMAGE_IMAGE:
    ∀f s a b. BIJ f a b ∧ s ⊆ a ⇒ (PREIMAGE f (IMAGE f s) ∩ a = s)
Proof
    rw[] >> irule SUBSET_ANTISYM >> rw[PREIMAGE_IMAGE] >> rw[SUBSET_DEF] >>
    fs[PREIMAGE_def] >> `x' ∈ a` by fs[SUBSET_DEF] >>
    fs[BIJ_DEF,INJ_DEF] >> qpat_x_assum `∀x y. _` (qspecl_then [`x`,`x'`] assume_tac) >> rfs[]
QED

Theorem BIJ_POW:
    ∀f s t. BIJ f s t ⇒ BIJ (IMAGE f) (POW s) (POW t)
Proof
    rw[] >> rw[BIJ_ALT,EXISTS_UNIQUE_THM]
    >- (fs[BIJ_ALT,EXISTS_UNIQUE_THM,FUNSET,POW_DEF,SUBSET_DEF] >> rw[] >> RES_TAC >> RES_TAC)
    >- (qexists_tac `PREIMAGE f y ∩ s` >> simp[IN_PREIMAGE,POW_DEF] >>
        irule (GSYM BIJ_IMAGE_PREIMAGE) >> qexists_tac `t` >> fs[POW_DEF])
    >- (rename [`a = b`] >> `PREIMAGE f (IMAGE f b) ∩ s = PREIMAGE f (IMAGE f a) ∩ s` by rw[] >>
        `PREIMAGE f (IMAGE f b) ∩ s = b` by (irule BIJ_PREIMAGE_IMAGE >> fs[POW_DEF] >>
            qexists_tac `t` >> rw[]) >>
        `PREIMAGE f (IMAGE f a) ∩ s = a` by (irule BIJ_PREIMAGE_IMAGE >> fs[POW_DEF] >>
            qexists_tac `t` >> rw[]) >>
        fs[])
QED

Theorem DISJOINT_CROSS:
    ∀s0 s1 t0 t1. DISJOINT (s0 × s1) (t0 × t1) ⇔ DISJOINT s0 t0 ∨ DISJOINT s1 t1
Proof
    rw[DISJOINT_DEF,EXTENSION] >> eq_tac >> rw[]
    >- (CCONTR_TAC >> fs[] >> qpat_x_assum `∀x. _` (qspec_then `(x,x')` assume_tac) >> rw[])
    >- (qpat_x_assum `∀x. _` (qspec_then `FST x` assume_tac) >> fs[])
    >- (qpat_x_assum `∀x. _` (qspec_then `SND x` assume_tac) >> fs[])
QED

Theorem CROSS_DIFF:
    ∀A B X Y. A ⊆ X ∧ B ⊆ Y ⇒ (X × Y DIFF A × B =
        ((X DIFF A) × (Y DIFF B)) ∪ ((X DIFF A) × B) ∪ (A × (Y DIFF B)))
Proof
    rw[] >> fs[CROSS_DEF,DIFF_DEF,UNION_DEF,EXTENSION,SUBSET_DEF] >> rw[] >>
    Cases_on `FST x ∈ X` >> Cases_on `SND x ∈ Y` >> Cases_on `FST x ∈ A` >> Cases_on `SND x ∈ B` >>
    fs[] >> RES_TAC
QED

Theorem CROSS_EQ:
    ∀A B X Y. (A × B = X × Y) ∧ (X × Y ≠ ∅) ⇒ (A = X) ∧ (B = Y)
Proof
    rw[CROSS_DEF,EXTENSION] >> rename [`y ∈ _ ⇔ y ∈ _`] >> last_assum (qspec_then `x` assume_tac)
    >- (last_x_assum (qspec_then `(y,SND x)` assume_tac) >> rfs[])
    >- (last_x_assum (qspec_then `(FST x,y)` assume_tac) >> rfs[])
QED

Theorem CROSS_UNION_LEFT:
    ∀r s t. (s ∪ t) × r = s × r ∪ t × r
Proof
    rw[CROSS_DEF,UNION_DEF,EXTENSION] >> eq_tac >> rw[] >> rw[]
QED

Theorem CROSS_UNION_RIGHT:
    ∀r s t. r × (s ∪ t) = r × s ∪ r × t
Proof
    rw[CROSS_DEF,UNION_DEF,EXTENSION] >> eq_tac >> rw[] >> rw[]
QED

Theorem POW_SING:
    ∀x. POW {x} = {{x}} ∪ {∅}
Proof
    rw[POW_DEF,EXTENSION,SUBSET_DEF] >> eq_tac >> rw[]
    >- (rename [`∀x. x ∈ s ⇒ x = y`] >> Cases_on `∀x. x ∉ s` >> rw[] >>
        rename [`x ∈ _ ⇔ _`] >> fs[] >> last_assum (drule_then assume_tac) >> fs[] >> pop_assum kall_tac >>
        eq_tac >> rw[])
    >- (rfs[])
    >- (rename [`x = y`,`x ∈ s`] >> last_x_assum (qspec_then `x` assume_tac) >> fs[])
QED

Theorem IN_POW_SING:
    ∀x y. x ∈ POW {y} ⇔ (x = {y}) ∨ (x = ∅)
Proof
    rw[POW_SING]
QED

Theorem MEMBER_EMPTY:
    ∀s. (∀x. x ∉ s) ⇔ (s = ∅)
Proof
    rw[EMPTY_DEF,EXTENSION]
QED

Theorem SUBSET_POW_SING:
    ∀s x. s ⊆ POW {x} ⇔ (s = POW {x}) ∨ (s = {{x}}) ∨ (s = {∅}) ∨ (s = ∅)
Proof
    rw[POW_SING] >> Q.RENAME_TAC [`s ⊆ {{y}} ∪ {∅}`] >>
    rw[SUBSET_DEF,UNION_DEF] >> eq_tac >> rw[] >> fs[] >>
    Cases_on `{y} ∈ s` >> Cases_on `∅ ∈ s` >> fs[]
    >- (`s = {x | (x = {y}) ∨ (x = ∅)}` suffices_by rw[] >> rw[EXTENSION] >> eq_tac >> rw[]
        >- (last_x_assum (dxrule_then assume_tac) >> fs[EXTENSION])
        >- (`x = {y}` by rw[EXTENSION] >> rw[])
        >- (fs[MEMBER_EMPTY]))
    >- (`s = {{y}}` suffices_by rw[] >> rw[EXTENSION] >> eq_tac >> rw[]
        >- (last_x_assum (drule_then assume_tac) >> fs[EXTENSION] >> fs[MEMBER_EMPTY])
        >- (`x = {y}` by rw[EXTENSION] >> rw[]))
    >- (`s = {∅}` suffices_by rw[] >> rw[EXTENSION] >> eq_tac >> rw[]
        >- (last_x_assum (drule_then assume_tac) >> fs[EXTENSION] >>
            `x = {y}` by rw[EXTENSION] >> fs[])
        >- (fs[MEMBER_EMPTY]))
    >- (`s = ∅` suffices_by rw[] >> rw[EXTENSION] >> CCONTR_TAC >> fs[] >>
        last_x_assum (drule_then assume_tac) >> fs[] >> fs[])
QED

Theorem COUNT_EMPTY:
    ∀n. (count n = ∅) ⇔ (n = 0)
Proof
    rw[count_def,EXTENSION] >> eq_tac >> rw[] >>
    Cases_on `n` >> simp[] >> rename [`SUC n`] >>
    pop_assum (qspec_then `n` assume_tac) >> fs[]
QED

(*
Theorem COUNT_ONE:
    count 1 = {0}
Proof
    fs[count_def,EXTENSION]
QED
*)

Theorem IMAGE_COUNT_ONE:
    ∀f. IMAGE f (count 1) = {f 0}
Proof
    fs[COUNT_ONE]
QED

Theorem IMAGE_PAIR:
    ∀s y. IMAGE (λx. (x,y)) s = s × {y}
Proof
    rw[EXTENSION,CROSS_DEF] >> eq_tac >> rw[] >> fs[] >>
    qexists_tac `FST x` >> rw[PAIR]
QED

Theorem IMAGE_LINV:
    ∀f r s t. BIJ f s t ∧ r ⊆ t ⇒ IMAGE (LINV f s) r = PREIMAGE f r ∩ s
Proof
    rw[SUBSET_DEF] >> simp[EXTENSION] >> qx_gen_tac `x` >> eq_tac >> rw[] >> TRY $ rename [`LINV f s y`]
    >- (`f (LINV f s y) = y` suffices_by simp[] >> irule BIJ_LINV_INV >> qexists_tac `t` >> fs[])
    >- (dxrule_then mp_tac BIJ_LINV_BIJ >> simp[BIJ_ALT,FUNSET])
    >- (qexists_tac `f x` >> simp[] >> irule EQ_SYM >>
        irule LINV_DEF >> simp[] >> qexists_tac `t` >> fs[BIJ_DEF])
QED

Theorem PREIMAGE_LINV:
    ∀f r s t. BIJ f s t ∧ r ⊆ s ⇒ PREIMAGE (LINV f s) r ∩ t = IMAGE f r
Proof
    rw[SUBSET_DEF] >> simp[EXTENSION] >> qx_gen_tac `y` >> eq_tac >> rw[]
    >- (qexists_tac `LINV f s y` >> simp[] >> irule EQ_SYM >>
        irule BIJ_LINV_INV >> qexists_tac `t` >> simp[])
    >- (`LINV f s (f x) = x` suffices_by simp[] >> irule LINV_DEF >> simp[] >>
        qexists_tac `t` >> fs[BIJ_DEF])
    >- (fs[BIJ_ALT,FUNSET])
QED

Theorem BIGUNION_POW:
    ∀s. BIGUNION (POW s) = s
Proof
    rw[EXTENSION,POW_DEF] >> eq_tac >> rw[]
    >- (rfs[SUBSET_DEF])
    >- (qexists_tac `s` >> fs[])
QED

Theorem BIGUNION_IMAGE_COUNT_ONE:
    ∀f. BIGUNION (IMAGE f (count 1)) = f 0
Proof
    fs[IMAGE_COUNT_ONE]
QED

Theorem BIGINTER_IMAGE_COUNT_ONE:
    ∀f. BIGINTER (IMAGE f (count 1)) = f 0
Proof
    fs[IMAGE_COUNT_ONE]
QED

Theorem BIGUNION_IMAGE_COUNT_SUC_COMM:
    ∀f n. BIGUNION (IMAGE f (count (SUC n))) = f n ∪ BIGUNION (IMAGE f (count n))
Proof
    rw[EXTENSION] >> eq_tac >> rw[]
    >- (rename [`m < SUC n`] >> Cases_on `x ∈ f n` >> fs[] >> qexists_tac `f m` >> fs[] >>
        qexists_tac `m` >> fs[] >> Cases_on `m = n` >> fs[])
    >- (qexists_tac `f n` >> fs[] >> qexists_tac `n` >> fs[])
    >- (rename [`m < n`] >> qexists_tac `f m` >> fs[] >>
        qexists_tac `m` >> fs[])
QED

Theorem BIGINTER_IMAGE_COUNT_SUC_COMM:
    ∀f n. BIGINTER (IMAGE f (count (SUC n))) = f n ∩ BIGINTER (IMAGE f (count n))
Proof
    rw[EXTENSION] >> eq_tac >> rw[]
    >- (qpat_x_assum `∀P. _` (qspec_then `f n` assume_tac) >> pop_assum irule >>
        qexists_tac `n` >> fs[])
    >- (rename [`m < n`] >> fs[] >> qpat_x_assum `∀P. _` (qspec_then `f m` assume_tac) >>
        pop_assum irule >> qexists_tac `m` >> fs[])
    >- (rename [`m < SUC n`] >> fs[] >> qpat_x_assum `∀P. _` (qspec_then `f m` assume_tac) >>
        Cases_on `m = n` >> fs[] >> first_x_assum irule >> qexists_tac `m` >> fs[])
QED

Theorem BIGINTER_IMAGE_COUNT_SUC:
    ∀f n. BIGINTER (IMAGE f (count (SUC n))) = BIGINTER (IMAGE f (count n)) ∩ f n
Proof
    rw[BIGINTER_IMAGE_COUNT_SUC_COMM,INTER_COMM]
QED

Theorem BIGUNION_IMAGE_COUNT_SUC:
    ∀f n. BIGUNION (IMAGE f (count (SUC n))) = BIGUNION (IMAGE f (count n)) ∪ f n
Proof
    rw[BIGUNION_IMAGE_COUNT_SUC_COMM,UNION_COMM]
QED

Theorem DIFF_BIGUNION1:
    ∀sp s. (s ≠ ∅) ⇒ (sp DIFF BIGUNION s = BIGINTER (IMAGE (λu. sp DIFF u) s))
Proof
    rpt strip_tac >> fs[GSYM MEMBER_NOT_EMPTY] >>
    `∀x. x ∈ sp ∧ x ∉ BIGUNION s ⇔ x ∈ BIGINTER (IMAGE (λu. sp DIFF u) s)`
        suffices_by (strip_tac >> fs[EXTENSION]) >>
    fs[IN_BIGINTER_IMAGE] >> strip_tac >> eq_tac >> rpt strip_tac >> fs[]
    >- (qpat_x_assum `∀s'. _` (qspec_then `u` assume_tac) >> rfs[])
    >- (RES_TAC)
    >- (CCONTR_TAC >> fs[] >> RES_TAC)
QED

Theorem DIFF_BIGINTER_IMAGE:
    ∀sp s f. s ≠ ∅ ∧ f ∈ FUNSET s (POW sp) ⇒
        (sp DIFF BIGINTER (IMAGE f s) = BIGUNION (IMAGE (λu. sp DIFF f u) s))
Proof
    rw[] >> rw[EXTENSION,IN_BIGUNION_IMAGE,IN_BIGINTER_IMAGE] >>
    eq_tac >> rw[] >> fs[] >> qexists_tac `u` >> fs[]
QED

Theorem DIFF_BIGUNION_IMAGE:
    ∀sp s f. s ≠ ∅ ∧ f ∈ FUNSET s (POW sp) ⇒
        (sp DIFF BIGUNION (IMAGE f s) = BIGINTER (IMAGE (λu. sp DIFF f u) s))
Proof
    rw[] >> rw[EXTENSION,IN_BIGUNION_IMAGE,IN_BIGINTER_IMAGE] >>
    eq_tac >> rw[] >> fs[FUNSET,POW_DEF]
    >- (qpat_x_assum `∀x. _` (qspec_then `u` assume_tac) >> rfs[])
    >- (fs[EXTENSION] >> RES_TAC)
    >- (CCONTR_TAC >> fs[] >> RES_TAC)
QED

Theorem BIGINTER_IMAGE_COUNT_INTER:
    ∀n m f g. BIGINTER (IMAGE f (count n)) ∩ BIGINTER (IMAGE g (count m)) =
        BIGINTER (IMAGE (λx. if x < n then f x else g (x − n)) (count (n + m)))
Proof
    rw[EXTENSION,IN_BIGINTER_IMAGE] >> eq_tac >> rw[]
    >- (rename [`k < m + n`] >> last_x_assum (qspec_then `k` assume_tac) >>
        last_x_assum (qspec_then `k - n` assume_tac) >> Cases_on `k < n` >> rfs[])
    >- (last_x_assum (qspec_then `y` assume_tac) >> rfs[])
    >- (last_x_assum (qspec_then `y + n` assume_tac) >> rfs[])
QED

Theorem BIGUNION_IMAGE_COUNT_UNION:
    ∀n m f g. BIGUNION (IMAGE f (count n)) ∪ BIGUNION (IMAGE g (count m)) =
        BIGUNION (IMAGE (λx. if x < n then f x else g (x − n)) (count (n + m)))
Proof
    rw[EXTENSION,IN_BIGUNION_IMAGE] >> eq_tac >> rw[] >> rename [`k < _`]
    >- (qexists_tac `k` >> fs[])
    >- (qexists_tac `k + n` >> fs[])
    >- (Cases_on `k < n` >> fs[] >> rw[]
        >- (DISJ1_TAC >> qexists_tac `k` >> fs[])
        >- (DISJ2_TAC >> qexists_tac `k - n` >> fs[]))
QED

Theorem BIGINTER_IMAGE_UNION_LEFT:
    ∀s t f. BIGINTER (IMAGE (λx. s ∪ f x) t) = s ∪ BIGINTER (IMAGE f t)
Proof
    rpt strip_tac >>
    `∀x. x ∈ BIGINTER (IMAGE (λx. s ∪ f x) t) ⇔ x ∈ s ∨ x ∈ BIGINTER (IMAGE f t)`
        suffices_by (strip_tac >> fs[EXTENSION]) >>
    fs[IN_BIGINTER_IMAGE] >> rpt strip_tac >> rpt strip_tac >> eq_tac >> rw[]
    >- (CCONTR_TAC >> fs[] >> RES_TAC)
    >- (fs[])
    >- (RES_TAC >> fs[])
QED

Theorem BIGUNION_IMAGE_INTER_LEFT:
    ∀s t f. BIGUNION (IMAGE (λx. s ∩ f x) t) = s ∩ BIGUNION (IMAGE f t)
Proof
    rpt strip_tac >>
    `∀x. x ∈ BIGUNION (IMAGE (λx. s ∩ f x) t) ⇔ x ∈ s ∧ x ∈ BIGUNION (IMAGE f t)`
        suffices_by (strip_tac >> fs[EXTENSION]) >>
    fs[IN_BIGUNION_IMAGE] >> rpt strip_tac >> rpt strip_tac >> eq_tac >> rw[]
    >- (fs[])
    >- (EXISTS_TAC ``x':β`` >> fs[])
QED

Theorem BIGUNION_IMAGE_UNION_LEFT:
    ∀s t f. t ≠ ∅ ⇒ BIGUNION (IMAGE (λx. s ∪ f x) t) = s ∪ BIGUNION (IMAGE f t)
Proof
    rw[] >> rw[EXTENSION,IN_BIGUNION_IMAGE] >> eq_tac >> rw[] >> fs[]
    >- (`∃x'. x' ∈ t ∧ x ∈ f x'` suffices_by rw[] >>
        EXISTS_TAC ``x' : β`` >> fs[])
    >- (fs[MEMBER_NOT_EMPTY])
    >- (EXISTS_TAC ``x' : β`` >> rw[])
QED

Theorem BIGINTER_IMAGE_INTER_LEFT:
    ∀s t f. t ≠ ∅ ⇒ BIGINTER (IMAGE (λx. s ∩ f x) t) = s ∩ BIGINTER (IMAGE f t)
Proof
    rw[] >> rw[EXTENSION,IN_BIGINTER_IMAGE] >> eq_tac >> rw[] >> fs[MEMBER_NOT_EMPTY]
QED

Theorem BIGINTER_IMAGE_UNION_RIGHT:
    ∀s t f. BIGINTER (IMAGE (λx. f x ∪ s) t) = BIGINTER (IMAGE f t) ∪ s
Proof
    fs[BIGINTER_IMAGE_UNION_LEFT,UNION_COMM]
QED

Theorem BIGUNION_IMAGE_INTER_RIGHT:
    ∀s t f. BIGUNION (IMAGE (λx. f x ∩ s) t) = BIGUNION (IMAGE f t) ∩ s
Proof
    fs[BIGUNION_IMAGE_INTER_LEFT,INTER_COMM]
QED

Theorem BIGUNION_IMAGE_UNION_LEFT:
    ∀s t f. t ≠ ∅ ⇒ BIGUNION (IMAGE (λx. f x ∪ s) t) = BIGUNION (IMAGE f t) ∪ s
Proof
    fs[BIGUNION_IMAGE_UNION_LEFT,UNION_COMM]
QED

Theorem BIGINTER_IMAGE_INTER_LEFT:
    ∀s t f. t ≠ ∅ ⇒ BIGINTER (IMAGE (λx. f x ∩ s) t) = BIGINTER (IMAGE f t) ∩ s
Proof
    fs[BIGINTER_IMAGE_INTER_LEFT,INTER_COMM]
QED

Theorem BIGUNION_IMAGE_EQUAL:
    ∀f g s. (∀x. x ∈ s ⇒ (f x = g x)) ⇒
        (BIGUNION (IMAGE f s) = BIGUNION (IMAGE g s))
Proof
    rw[EXTENSION,IN_BIGUNION_IMAGE] >> eq_tac >> rw[] >> rename [`n ∈ s`,`x ∈ _ n`] >>
    qexists_tac `n` >> rw[] >> last_x_assum (dxrule_then assume_tac) >> fs[]
QED

Theorem PREIMAGE_o_INTER:
    ∀X Y f g s. IMAGE f X ⊆ Y ⇒ PREIMAGE (g ∘ f) s ∩ X = PREIMAGE f (PREIMAGE g s ∩ Y) ∩ X
Proof
    rw[EXTENSION,IN_PREIMAGE] >> eq_tac >> rw[] >> fs[SUBSET_DEF,IN_IMAGE] >>
    last_x_assum irule >> qexists_tac `x` >> simp[]
QED

Theorem BIJ_NUM_TO_PAIR:
    BIJ num_to_pair 𝕌(:num) (𝕌(:num) × 𝕌(:num))
Proof
    fs[BIJ_IFF_INV] >> EXISTS_TAC ``pair_to_num`` >>
    fs[pair_to_num_inv] >> rw[] >>
    assume_tac (ISPEC ``x:num#num`` ABS_PAIR_THM) >> fs[pair_to_num_inv]
QED

Theorem BIJ_PAIR_TO_NUM:
    BIJ pair_to_num (𝕌(:num) × 𝕌(:num)) 𝕌(:num)
Proof
    fs[BIJ_IFF_INV] >> EXISTS_TAC ``num_to_pair`` >>
    fs[pair_to_num_inv] >> rw[] >>
    assume_tac (ISPEC ``x:num#num`` ABS_PAIR_THM) >> fs[pair_to_num_inv]
QED

Theorem BIJ_SWAP:
    BIJ SWAP (𝕌(:α) × 𝕌(:β)) (𝕌(:β) × 𝕌(:α))
Proof
    rw[BIJ_ALT,FUNSET,EXISTS_UNIQUE_DEF]
    >- (qexists_tac `SWAP y` >> simp[SWAP_def])
    >- (simp[PAIR_FST_SND_EQ] >> fs[SWAP_def])
QED

Theorem FINITE_SURJ_COUNT_EQ:
    ∀s. FINITE s ⇔ ∃c n. SURJ c (count n) s
Proof
    rw[] >> eq_tac >> rw[]
    >- (Induct_on `s` >> rw[]
        >- (map_every EXISTS_TAC [``_ : num -> α``,``0 : num``] >> fs[count_def,SURJ_DEF])
        >- (map_every EXISTS_TAC [``λi : num. if i < n then (c i) else e : α``,``SUC n``] >>
            fs[count_def,SURJ_DEF] >> rw[]
            >- (EXISTS_TAC ``n:num`` >> fs[])
            >- (RES_TAC >> EXISTS_TAC ``y:num`` >> fs[])))
    >- (imp_res_tac FINITE_SURJ >> rfs[])
QED

Theorem FINITE_INJ_COUNT_EQ:
    ∀s. FINITE s ⇔ ∃c n. INJ c s (count n)
Proof
    rw[] >> eq_tac >> rw[]
    >- (fs[FINITE_SURJ_COUNT_EQ] >> rw[Once SWAP_EXISTS_THM] >> qexists_tac `n` >>
        irule SURJ_IMP_INJ >> fs[SWAP_EXISTS_THM] >> qexists_tac `c` >> rw[])
    >- ((dxrule_then assume_tac) inj_surj >> fs[] >> rw[FINITE_SURJ_COUNT_EQ] >>
        rename [`SURJ f _ _`] >> map_every qexists_tac [`f`,`n`] >> rw[])
QED

Theorem ITSET_SING:
    ∀f x a. ITSET f {x} a = f x a
Proof
    rw[] >> fs[ITSET_THM]
QED

Theorem SUBSET_IMP_DIFFS_SUBSET:
    ∀a b s. a ⊆ b ⇒ s DIFF b ⊆ s DIFF a
Proof
    rw[SUBSET_DEF,DIFF_DEF] >> CCONTR_TAC >> fs[] >> RES_TAC
QED

Theorem DIFF_SING_EMPTY:
    ∀s x. (s DIFF {x} = ∅) ⇔ (s = ∅) ∨ (s = {x})
Proof
    rw[] >> eq_tac >> rw[]
    >- (Cases_on `s = ∅` >> rw[] >> fs[EXTENSION] >> rw[] >> rename [`z ∈ _ ⇔ _`,`y ∈ s`] >>
        last_x_assum (fn th => map_every (fn tm => (qspec_then tm assume_tac) th) [`y`,`z`]) >>
        rfs[] >> fs[] >> CCONTR_TAC >> fs[])
    >- (rw[EMPTY_DIFF])
    >- (rw[DIFF_EQ_EMPTY])
QED

Theorem surj_countable:
    ∀f s t. countable s ∧ SURJ f s t ⇒ countable t
Proof
    rw[] >> dxrule_then assume_tac image_countable >>
    pop_assum (qspec_then `f` assume_tac) >> irule subset_countable >>
    qexists_tac `IMAGE f s` >> rw[] >> fs[IMAGE_SURJ]
QED

Theorem preimage_bij_countable:
    ∀f s a b. BIJ f a b ∧ s ⊆ b ∧ countable s ⇒ countable (PREIMAGE f s ∩ a)
Proof
    rw[] >> irule (INST_TYPE [alpha |-> ``:β``,beta |-> ``:α``] surj_countable) >>
    drule_then assume_tac BIJ_INV >> fs[] >> map_every qexists_tac [`g`,`s`] >>
    simp[SURJ_DEF,IN_PREIMAGE] >> fs[BIJ_ALT,EXISTS_UNIQUE_THM,FUNSET] >> rw[]
    >- (`x ∈ b` by fs[SUBSET_DEF] >> fs[])
    >- (`x ∈ b` by fs[SUBSET_DEF] >> fs[])
    >- (qexists_tac `f x` >> fs[])
QED

(*---------------------------------------------------------------------------*)
(* Trivial stuff for Lists *)
(*---------------------------------------------------------------------------*)

Definition PROD:
    PROD [] = 1:num ∧
    PROD (h::t) = h * PROD t
End

Definition SUBLIST_DEF:
    SUBLIST (n,m) l = TAKE m (DROP n l)
End

Definition REMOVE_DEF:
    REMOVE [] n = NONE ∧
    REMOVE (sh::st) 0 = SOME st ∧
    REMOVE (sh::st) (SUC n) = do
        nt <- REMOVE st n;
        return (sh::nt) od
End

Theorem DROP_ALT:
    (∀l. DROP 0 l = l) ∧
    (∀n. DROP n [] = []) ∧
    (∀ n h t. DROP (SUC n) (h::t) = DROP n t)
Proof
    rw[DROP_def]
QED

Theorem TAKE_ALT:
    (∀l. TAKE 0 l = []) ∧
    (∀n. TAKE n [] = []) ∧
    (∀ n h t. TAKE (SUC n) (h::t) = (h::TAKE n t))
Proof
    rw[TAKE_def]
QED

Theorem oEL_ALT:
    (∀n. oEL n [] = NONE) ∧
    (∀h t. oEL 0 (h::t) = SOME h) ∧
    (∀n h t. oEL (SUC n) (h::t) = oEL n t)
Proof
    rw[oEL_def]
QED

Theorem LENGTH_REMOVE:
    ∀l n r. REMOVE l n = SOME r ⇒ LENGTH l = SUC (LENGTH r)
Proof
    Induct_on `l` >> rw[REMOVE_DEF] >> Cases_on `n` >> fs[REMOVE_DEF] >>
    rename [`REMOVE l n = _`] >> last_x_assum (dxrule_then assume_tac) >> rw[]
QED

Theorem MAP_FST_ZIP:
    ∀l1 l2. LENGTH l1 = LENGTH l2 ⇒ MAP FST (ZIP (l1,l2)) = l1
Proof
    rw[MAP_ZIP]
QED

Theorem MAP_SND_ZIP:
    ∀l1 l2. LENGTH l1 = LENGTH l2 ⇒ MAP SND (ZIP (l1,l2)) = l2
Proof
    rw[MAP_ZIP]
QED

Theorem ZIP_SNOC:
    ∀x1 x2 l1 l2. LENGTH l1 = LENGTH l2 ⇒  ZIP (SNOC x1 l1,SNOC x2 l2) = SNOC (x1,x2) (ZIP (l1,l2))
Proof
    NTAC 3 strip_tac >> Induct_on `l1` >> rw[] >> Cases_on `l2` >> rw[] >> fs[]
QED

Theorem TAKE_SUC_SNOC:
    ∀n l. n < LENGTH l ⇒ TAKE (SUC n) l = SNOC (EL n l) (TAKE n l)
Proof
    Induct_on `n` >- (rw[] >> Cases_on `l` >> fs[]) >>
    NTAC 2 strip_tac >> Cases_on `l` >- (fs[]) >>
    last_x_assum (fn th => fs[] >> (dxrule_then assume_tac) th) >> simp[]
QED

Theorem DROP_EL_SUC:
    ∀l n. n < LENGTH l ⇒ DROP n l = EL n l :: DROP (SUC n) l
Proof
    Induct_on `l` >> rw[] >> Cases_on `n` >> rw[]
QED

Definition REV_CHOICE_LIST_DEF:
    REV_CHOICE_LIST s = ITSET CONS s []
End

Theorem REV_CHOICE_LIST_ALT:
    ∀s. FINITE s ⇒ REV_CHOICE_LIST s = REVERSE (SET_TO_LIST s)
Proof
    rw[] >> simp[REV_CHOICE_LIST_DEF,ITSET_eq_FOLDL_SET_TO_LIST,REVERSE_FOLDL] >>
    `C CONS = λl x. x ::l` suffices_by simp[] >> simp[FUN_EQ_THM]
QED

Theorem ITSET_TO_FOLDR:
    ∀f s b. FINITE s ⇒ ITSET f s b = FOLDR f b (REV_CHOICE_LIST s)
Proof
    rw[ITSET_eq_FOLDL_SET_TO_LIST,FOLDL_FOLDR_REVERSE,REV_CHOICE_LIST_ALT,SF ETA_ss]
QED

(*---------------------------------------------------------------------------*)
(* Trivial stuff for Finite Maps *)
(*---------------------------------------------------------------------------*)

Theorem FUPDATE_LIST_MEM_KEY_MEM_VAL:
    ∀kvl f k. MEM k (MAP FST kvl) ⇒ MEM ((f |++ kvl) ' k) (MAP SND kvl)
Proof
    HO_MATCH_MP_TAC SNOC_INDUCT >> rw[FUPDATE_LIST_SNOC] >>
    Cases_on `x` >> fs[FAPPLY_FUPDATE_THM,MAP_SNOC] >> rw[]
QED

Theorem FUPDATE_LIST_MAP_VAL:
    ∀kvl f1 f2 g k. MEM k (MAP FST kvl) ⇒
    (f1 |++ ZIP (MAP FST kvl,MAP g (MAP SND kvl))) ' k = g ((f2 |++ kvl) ' k)
Proof
    HO_MATCH_MP_TAC SNOC_INDUCT >> rw[] >>
    `LENGTH (MAP FST kvl) = LENGTH (MAP g (MAP SND kvl))` by fs[LENGTH_MAP] >>
    rw[FUPDATE_LIST_SNOC,MAP_SNOC,ZIP_SNOC] >>
    Cases_on `x` >> fs[FAPPLY_FUPDATE_THM] >> rw[] >>
    last_x_assum irule >> fs[MAP_SNOC]
QED

(*---------------------------------------------------------------------------*)
(* Trivial stuff for Reals *)
(*---------------------------------------------------------------------------*)

val _ = augment_srw_ss [realSimps.REAL_ARITH_ss];

Theorem REAL_NE_LT_TOTAL:
    ∀x:real y. x ≠ y ⇔ x < y ∨ y < x
Proof
    simp[]
QED

Theorem REAL_SUP_ADD:
    ∀p q. (∃pel. p pel) ∧ (∃pub. ∀x. p x ⇒ x ≤ pub) ∧ (∃qel. q qel) ∧ (∃qub. ∀y. q y ⇒ y ≤ qub) ⇒
        sup p + sup q = sup {x + y:real | p x ∧ q y}
Proof
    rw[GSYM REAL_LE_ANTISYM]
    >- (map_every qabbrev_tac [`sup_pq = sup p + sup q`,`pq = {x + y | p x ∧ q y}`] >>
        `(sup_pq ≤ sup pq ⇔ ∀y. (∀z. pq z ⇒ z ≤ y) ⇒ sup_pq ≤ y)` by (
            irule REAL_LE_SUP >> map_every qunabbrev_tac [`sup_pq`,`pq`] >> rw[]
            >- (map_every qexists_tac [`pel + qel`,`(pel,qel)`] >> simp[]) >>
            qexists_tac `pub + qub` >> rw[] >>
            rename [`(z,T) = _ xy`] >> Cases_on `xy` >> rename [`_ = _ (a,b)`] >> fs[] >>
            irule REAL_LE_ADD2 >> rw[]) >>
        fs[] >> map_every qunabbrev_tac [`sup_pq`,`pq`] >> rw[] >>
        qpat_x_assum `_ ⇔ _` kall_tac >> rename [`_ ≤ pqub`] >>
        simp[GSYM REAL_LE_SUB_LADD] >> irule REAL_IMP_SUP_LE >> REVERSE (rw[])
        >- (qexists_tac `pel` >> simp[]) >> rename [`a ≤ _`] >>
        simp[REAL_LE_SUB_LADD] >> SIMP_TAC pure_ss [Once REAL_ADD_COMM] >>
        simp[GSYM REAL_LE_SUB_LADD] >> irule REAL_IMP_SUP_LE >> REVERSE (rw[])
        >- (qexists_tac `qel` >> simp[]) >> rename [`b ≤ _`] >>
        simp[REAL_LE_SUB_LADD] >> SIMP_TAC pure_ss [Once REAL_ADD_COMM] >>
        last_x_assum irule >> qexists_tac `(a,b)` >> fs[])
    >- (irule REAL_IMP_SUP_LE >> REVERSE (rw[])
        >- (map_every qexists_tac [`pel + qel`,`(pel,qel)`] >> simp[]) >>
        rename [`(z,T) = _ xy`] >> Cases_on `xy` >> rename [`_ = _ (a,b)`] >> fs[] >>
        irule REAL_LE_ADD2 >> rw[] >> irule REAL_SUP_UBOUND_LE >> fs[] >> rw[]
        >| [qexists_tac `pel`,qexists_tac `pub`,qexists_tac `qel`,qexists_tac `qub`] >> simp[])
QED

Theorem REAL_SUP_CMUL:
    ∀p c. (∃e. p e) ∧ (∃ub. ∀x. p x ⇒ x ≤ ub) ∧ 0 ≤ c ⇒
        c * sup p = sup {c * x:real | p x}
Proof
    rw[] >> REVERSE (fs[Once REAL_LE_LT]) >> fs[GSYM REAL_LE_LT]
    >- (`{0 | x | p x} = (λr:real. r = 0)` suffices_by (rw[REAL_SUP_CONST]) >>
        rw[FUN_EQ_THM] >> eq_tac >> rw[] >> qexists_tac `e` >> simp[]) >>
    rw[GSYM REAL_LE_ANTISYM]
    >- (`sup p ≤ c⁻¹ * sup {c * x | p x}` suffices_by simp[] >>
        irule REAL_IMP_SUP_LE >> REVERSE (rw[]) >- (qexists_tac `e` >> simp[]) >>
        irule REAL_SUP_UBOUND_LE >> rw[] >| [qexists_tac `e`,qexists_tac `c * ub`] >> rw[] >>
        rename [`c * x`] >> simp[])
    >- (irule REAL_IMP_SUP_LE >> REVERSE (rw[]) >- (qexists_tac `e` >> simp[]) >>
        fs[REAL_LE_LMUL] >> irule REAL_SUP_UBOUND_LE >> rw[]
        >| [qexists_tac `x`,qexists_tac `ub`] >> simp[])
QED

Theorem POS_IMP_LE_ABS:
    ∀x:real y. 0 ≤ x ∧ x ≤ y ⇒ abs x ≤ abs y
Proof
    rw[abs]
QED

Theorem NEG_IMP_LE_ABS:
    ∀x:real y. y ≤ x ∧ x ≤ 0 ⇒ abs x ≤ abs y
Proof
    rw[abs]
QED

Theorem REAL_LE_RMUL_NEG_IMP:
    ∀a:real b c. a ≤ 0 ∧ b ≤ c ⇒ c * a ≤ b * a
Proof
    simp[REAL_LE_LMUL_NEG_IMP]
QED

Theorem REAL_CLOSED_INTERVAL_MUL:
    ∀a:real b c d x y. a ≤ x ∧ x ≤ b ∧ c ≤ y ∧ y ≤ d ⇒
        -max (abs a) (abs b) * max (abs c) (abs d) ≤ x * y ∧
        x * y ≤ max (abs a) (abs b) * max (abs c) (abs d)
Proof
    simp[REAL_MUL_LNEG,GSYM ABS_BOUNDS] >> rw[] >>
    simp[ABS_MUL] >> irule REAL_LE_MUL2 >> simp[REAL_LE_MAX]
QED

Theorem REAL_MUL_SIGN:
    (∀x:real y. 0 ≤ x * y ⇔ (0 ≤ x ∧ 0 ≤ y) ∨ (x ≤ 0 ∧ y ≤ 0)) ∧
    (∀x:real y. x * y ≤ 0 ⇔ (0 ≤ x ∧ y ≤ 0) ∨ (x ≤ 0 ∧ 0 ≤ y))
Proof
    rw[] >> eq_tac >> rw[] >> fs[GSYM REAL_NEG_GE0,Excl "REAL_NEG_GE0"]
    >| (fn tc => [all_tac,tc,tc,all_tac,tc,tc]) $ dxrule_all_then assume_tac $ REAL_LE_MUL >>
    fs[] >> pop_assum mp_tac >> CONV_TAC CONTRAPOS_CONV >> rw[] >> fs[real_lte] >>
    fs[GSYM REAL_NEG_GT0,Excl "REAL_NEG_GT0"] >>
    dxrule_all_then assume_tac $ REAL_LT_MUL >> simp[]
QED

Theorem REAL_LT_MUL_NEG:
    ∀x:real y. x < 0 ∧ y < 0 ⇒ 0 < x * y
Proof
    rw[] >> qspecl_then [`-0`,`-x`,`-0`,`-y`] assume_tac REAL_LT_MUL2 >> rfs[]
QED

Theorem POW_BOUND_01:
    ∀r:real n. 0 ≤ r ∧ r ≤ 1 ⇒ 0 ≤ r pow n ∧ r pow n ≤ 1
Proof
    NTAC 3 strip_tac >> Induct_on `n` >> rw[pow] >>
    qspecl_then [`r`,`1`,`r pow n`,`1`] assume_tac REAL_LE_MUL2 >> rfs[]
QED

Theorem REAL_SUB_ASSOC:
    ∀x:real y z. x + (y - z) = x + y - z
Proof
    simp[real_sub,REAL_ADD_ASSOC]
QED

Theorem REAL_SUB_TRIANGLE_NEG:
    ∀a:real b c. a − b - (c − b) = a − c
Proof
    rw[]
QED

Theorem SUM_FIRST:
    ∀f m n. sum (m,SUC n) f = f m + sum (m,n) (f ∘ SUC)
Proof
    NTAC 2 strip_tac >> Induct_on `n` >- (simp[sum]) >>
    simp[sum,REAL_ADD_ASSOC,GSYM ADD_SUC]
QED

(*---------------------------------------------------------------------------*)
(* Trivial stuff for Limits *)
(*---------------------------------------------------------------------------*)

Theorem DIFF_POS_MONO:
    ∀f g x y. x < y ∧ (∀z. x ≤ z ∧ z ≤ y ⇒ f contl z) ∧
        (∀z. x < z ∧ z < y ⇒ (f diffl g z) z) ∧ (∀z. x < z ∧ z < y ⇒ 0 ≤ g z) ⇒
        f x ≤ f y
Proof
    rw[] >>
    `∀z. x < z ∧ z < y ⇒ f differentiable z` by (
        rw[differentiable] >> qexists_tac `g z` >> simp[]) >>
    drule_all_then assume_tac MVT >> fs[] >> simp[Once $ GSYM REAL_SUB_LE] >>
    irule REAL_LE_MUL >> simp[REAL_SUB_LE,REAL_LT_IMP_LE] >>
    `l = g z` suffices_by simp[] >> irule DIFF_UNIQ >> qexistsl_tac [`f`,`z`] >> simp[]
QED

(*---------------------------------------------------------------------------*)
(* Trivial stuff for Transcendentals *)
(*---------------------------------------------------------------------------*)

Theorem CONT_EXP:
    ∀x. exp contl x 
Proof
    rw[] >> irule DIFF_CONT >> qexists_tac `exp x` >> simp[DIFF_EXP]
QED

Theorem MCLAURIN_GEN:
    ∀f diff n. diff 0 = f ∧ (∀m. m < n ⇒ ∀t. (diff m diffl diff (SUC m) t) t) ⇒
        ∀x. ∃t. 0 ≤ x * t ∧ abs t ≤ abs x ∧
        f x = sum (0,n) (λm. diff m 0 / &FACT m * x pow m) + diff n t / &FACT n * x pow n
Proof
    rw[] >> Cases_on `n`
    >- (rw[] >> qexists_tac `x` >> simp[] >> CONV_TAC EVAL >> simp[]) >>
    rename [`SUC n`] >> Cases_on `x = 0`
    >- (rw[] >> qexists_tac `0` >> simp[POW_0,SUM_FIRST,o_DEF,SUM_0] >> CONV_TAC EVAL >> simp[]) >>
    fs[REAL_NE_LT_TOTAL]
    >- (qspecl_then [`diff 0`,`diff`,`x`,`SUC n`] assume_tac MCLAURIN_NEG >> rfs[] >>
        qexists_tac `t` >> simp[REAL_LE_LT,REAL_LT_MUL_NEG])
    >- (qspecl_then [`diff 0`,`diff`,`x`,`SUC n`] assume_tac MCLAURIN >> rfs[] >>
        qexists_tac `t` >> simp[REAL_LE_LT,REAL_LT_MUL])
QED

Theorem ABS_EXP:
    ∀x:real. abs (exp x) = exp x
Proof
    rw[EXP_POS_LE]
QED

(*---------------------------------------------------------------------------*)
(* Trivial stuff for Real Sigma (and Pi) *)
(*---------------------------------------------------------------------------*)

Theorem REAL_SUM_IMAGE_CDIV:
    ∀P. FINITE P ⇒ ∀f (c:real). ∑ (λx. f x / c) P = ∑ f P / c
Proof
    simp[real_div,REAL_SUM_IMAGE_CMUL]
QED

Theorem REAL_SUM_IMAGE_EMPTY:
    ∀(f:α -> real). ∑ f ∅ = 0
Proof
    simp[REAL_SUM_IMAGE_DEF,ITSET_EMPTY]
QED

Theorem REAL_SUM_IMAGE_INSERT:
    ∀(f:α -> real) e s. FINITE s ⇒ ∑ f (e INSERT s) = f e + ∑ f (s DELETE e)
Proof
    rw[REAL_SUM_IMAGE_DEF] >>
    qspecl_then [`λe acc. f e + acc`,`e`,`s`,`0r`]
        (irule o SIMP_RULE (srw_ss ()) []) COMMUTING_ITSET_RECURSES >>
    simp[]
QED

Definition REAL_PROD_IMAGE_DEF:
    REAL_PROD_IMAGE f s = ITSET (λe acc. f e * acc) s (1:real)
End
val _ = overload_on ("∏", Term `REAL_PROD_IMAGE`);

Theorem REAL_PROD_IMAGE_EMPTY:
    ∀(f:α -> real). ∏ f ∅ = 1
Proof
    simp[REAL_PROD_IMAGE_DEF,ITSET_EMPTY]
QED

Theorem REAL_PROD_IMAGE_INSERT:
    ∀(f:α -> real) e s. FINITE s ⇒ ∏ f (e INSERT s) = f e * ∏ f (s DELETE e)
Proof
    rw[REAL_PROD_IMAGE_DEF] >>
    qspecl_then [`λe acc. f e * acc`,`e`,`s`,`1r`]
        (irule o SIMP_RULE (srw_ss ()) []) COMMUTING_ITSET_RECURSES >>
    simp[]
QED

Theorem REAL_PROD_IMAGE_THM:
    ∀f. ∏ f ∅ = 1r ∧
        ∀e s. FINITE s ⇒ ∏ f (e INSERT s) = f e * ∏ f (s DELETE e)
Proof
    simp[REAL_PROD_IMAGE_EMPTY,REAL_PROD_IMAGE_INSERT]
QED

Theorem EXP_SUM:
    ∀(f:α -> real) s. FINITE s ⇒ exp (∑ f s) = ∏ (exp ∘ f) s
Proof
    strip_tac >> Induct_on `s` >>
    rw[REAL_SUM_IMAGE_THM,REAL_PROD_IMAGE_THM,EXP_0,DELETE_NON_ELEMENT_RWT,EXP_ADD]
QED

(*---------------------------------------------------------------------------*)
(* Trivial stuff for Floats *)
(*---------------------------------------------------------------------------*)

Definition float_not_equal_def:
    float_not_equal x y ⇔ case float_compare x y of LT => T | EQ => F | GT => T | UN => F
End

(*---------------------------------------------------------------------------*)
(* Trivial stuff for Extreals *)
(*---------------------------------------------------------------------------*)

Definition closed_interval_def:
    closed_interval a b = {x | a ≤ x ∧ x ≤ b}
End

Theorem normal_0:
    Normal 0 = 0
Proof
    simp[extreal_eq_zero]
QED

Theorem normal_1:
    Normal 1 = 1
Proof
    simp[extreal_of_num_def]
QED

Theorem normal_minus1:
    Normal (-1) = -1
Proof
    `Normal (-1) = -(Normal 1)` suffices_by simp[normal_1] >> simp[extreal_ainv_def]
QED

Theorem extreal_le_simp:
    (∀x y. Normal x ≤ Normal y ⇔ x ≤ y) ∧ (∀x. −∞ ≤ x ⇔ T) ∧ (∀x. x ≤ +∞ ⇔ T) ∧
    (∀x. Normal x ≤ −∞ ⇔ F) ∧ (∀x. +∞ ≤ Normal x ⇔ F) ∧ (+∞ ≤ −∞ ⇔ F)
Proof
    rw[extreal_le_def] >> Cases_on `x` >> simp[extreal_le_def]
QED

val _ = mk_local_simp "extreal_le_simp";

Theorem extreal_lt_simp:
    (∀x y. Normal x < Normal y ⇔ x < y) ∧ (∀x. x < −∞ ⇔ F) ∧ (∀x. +∞ < x ⇔ F) ∧
    (∀x. Normal x < +∞ ⇔ T) ∧ (∀x. −∞ < Normal x ⇔ T) ∧ (−∞ < +∞ ⇔ T)
Proof
    simp[extreal_lt_eq] >> rw[extreal_lt_def]
QED

val _ = mk_local_simp "extreal_lt_simp";

Theorem extreal_0_simp:
    (0 ≤ +∞ ⇔ T) ∧ (0 < +∞ ⇔ T) ∧ (+∞ ≤ 0 ⇔ F) ∧ (+∞ < 0 ⇔ F) ∧ (0 = +∞ ⇔ F) ∧ (+∞ = 0 ⇔ F) ∧
    (0 ≤ −∞ ⇔ F) ∧ (0 < −∞ ⇔ F) ∧ (−∞ ≤ 0 ⇔ T) ∧ (−∞ < 0 ⇔ T) ∧ (0 = −∞ ⇔ F) ∧ (−∞ = 0 ⇔ F) ∧
    (∀r. 0 ≤ Normal r ⇔ 0 ≤ r) ∧ (∀r. 0 < Normal r ⇔ 0 < r) ∧ (∀r. 0 = Normal r ⇔ r = 0) ∧
    (∀r. Normal r ≤ 0 ⇔ r ≤ 0) ∧ (∀r. Normal r < 0 ⇔ r < 0) ∧ (∀r. Normal r = 0 ⇔ r = 0)
Proof
    simp[GSYM normal_0]
QED

val _ = mk_local_simp "extreal_0_simp";

Theorem ineq_imp:
    (∀x:extreal y. x < y ⇒ ¬(y < x)) ∧ (∀x:extreal y. x < y ⇒ x ≠ y) ∧ (∀x:extreal y. x < y ⇒ ¬(y ≤ x)) ∧ 
    (∀x:extreal y. x < y ⇒ x ≤ y) ∧ (∀x:extreal y. x ≤ y ⇒ ¬(y < x))
Proof
    rw[] >> Cases_on `x` >> Cases_on `y` >> fs[]
QED

Theorem max_normal:
    ∀a b. max (Normal a) (Normal b) = Normal (max a b)
Proof
    rw[extreal_max_def,max_def]
QED

Theorem min_normal:
    ∀a b. min (Normal a) (Normal b) = Normal (min a b)
Proof
    rw[extreal_min_def,min_def]
QED

Theorem min_alt:
    (∀x. min +∞ x = x) ∧ (∀x. min x +∞ = x) ∧ (∀x. min −∞ x = −∞) ∧ (∀x. min x −∞ = −∞) ∧
    (∀x y. min (Normal x) (Normal y) = Normal (min x y))
Proof
    simp[min_infty] >> rw[extreal_min_def,min_def]
QED

Theorem max_alt:
    (∀x. max +∞ x = +∞) ∧ (∀x. max x +∞ = +∞) ∧ (∀x. max −∞ x = x) ∧ (∀x. max x −∞ = x) ∧
    (∀x y. max (Normal x) (Normal y) = Normal (max x y))
Proof
    simp[max_infty] >> rw[extreal_max_def,max_def]
QED

Theorem extreal_pow_alt:
    (∀x:extreal. x pow 0 = 1) ∧
    (∀n x:extreal. x pow (SUC n) = x pow n * x)
Proof
    simp[pow_0,ADD1,pow_add,pow_1]
QED

Theorem pow_even_le:
    ∀n. EVEN n ⇒ ∀x. 0 ≤ x pow n
Proof
    rw[] >> Cases_on `0 ≤ x` >- simp[pow_pos_le] >> fs[GSYM extreal_lt_def] >> simp[le_lt,pow_pos_even]
QED

Theorem pow_ainv_odd:
    ∀n. ODD n ⇒ ∀x. -x pow n = -(x pow n)
Proof
    rw[] >> qspecl_then [`n`,`-1`,`x`] mp_tac pow_mul >> simp[GSYM neg_minus1] >>
    `-1 pow n = -1` suffices_by simp[GSYM neg_minus1] >> completeInduct_on `n` >> fs[extreal_pow_alt] >>
    NTAC 2 (Cases_on `n` >> fs[extreal_pow_alt,ODD] >> rename [`ODD n`]) >> rw[GSYM neg_minus1]
QED

Theorem pow_ainv_even:
    ∀n. EVEN n ⇒ ∀x. -x pow n = x pow n
Proof
    rw[] >> qspecl_then [`n`,`-1`,`x`] mp_tac pow_mul >> simp[GSYM neg_minus1] >>
    `-1 pow n = 1` suffices_by simp[] >> completeInduct_on `n` >> fs[extreal_pow_alt] >>
    NTAC 2 (Cases_on `n` >> fs[extreal_pow_alt,EVEN] >> rename [`EVEN n`]) >> rw[GSYM neg_minus1]
QED

Theorem fn_plus_alt:
    ∀f. f⁺ = (λx. if 0 ≤ f x then f x else (0: extreal))
Proof
    rw[fn_plus_def,FUN_EQ_THM] >> qspecl_then [`f x`,`0`] assume_tac lt_total >>
    FULL_SIMP_TAC bool_ss [] >> simp[ineq_imp]
QED

Theorem FN_PLUS_FFMUL:
    ∀f g. (λx. f x * g x)⁺ = (λx. f⁺ x * g⁺ x + f⁻ x * g⁻ x)
Proof
    rw[FUN_EQ_THM,FN_PLUS_ALT',extreal_max_def,fn_minus_def,extreal_lt_def] >>
    Cases_on `0 ≤ f x` >> Cases_on `0 ≤ g x` >> simp[]
    >- simp[le_mul] >> fs[GSYM extreal_lt_def]
    >- (Cases_on `f x = 0` >> simp[] >> `0 < f x` by simp[lt_le] >> simp[GSYM extreal_not_lt,mul_lt])
    >- (Cases_on `g x = 0` >> simp[] >> `0 < g x` by simp[lt_le] >> simp[GSYM extreal_not_lt,mul_lt2])
    >- simp[lt_mul_neg,le_lt,neg_mul2]
QED

Theorem FN_MINUS_FFMUL:
    ∀f g. (λx. f x * g x)⁻ = (λx. f⁺ x * g⁻ x + f⁻ x * g⁺ x)
Proof
    rw[FUN_EQ_THM,FN_PLUS_ALT',extreal_max_def,fn_minus_def,extreal_lt_def] >>
    Cases_on `0 ≤ f x` >> Cases_on `0 ≤ g x` >> simp[]
    >- simp[le_mul] >> fs[GSYM extreal_lt_def]
    >- (Cases_on `f x = 0` >> simp[] >> `0 < f x` by simp[lt_le] >> simp[mul_lt,mul_rneg])
    >- (Cases_on `g x = 0` >> simp[] >> `0 < g x` by simp[lt_le] >> simp[mul_lt2,mul_lneg])
    >- (simp[lt_le] >> simp[GSYM extreal_not_lt,lt_mul_neg])
QED

Theorem FN_PLUS_NOT_NEG_INFTY:
    ∀f x. f⁺ x ≠ −∞
Proof
    rw[] >> irule pos_not_neginf >> simp[FN_PLUS_POS]
QED

Theorem FN_MINUS_NOT_NEG_INFTY:
    ∀f x. f⁻ x ≠ −∞
Proof
    rw[] >> irule pos_not_neginf >> simp[FN_MINUS_POS]
QED

Theorem sup_to_bool:
    (∀p. (sup p = +∞) ⇔ ∀x. (∀y. p y ⇒ y ≤ x) ⇒ x = +∞) ∧
    (∀p. (sup p = −∞) ⇔ ¬(∀x. (∀y. p y ⇒ y ≤ x) ⇒ x = +∞) ∧ ∀x. p x ⇒ x = −∞) ∧
    (∀p r. (sup p = Normal r) ⇔ ¬(∀x. (∀y. p y ⇒ y ≤ x) ⇒ x = +∞) ∧ ¬(∀x. p x ⇒ x = −∞) ∧ r = sup (λz. p (Normal z)))
Proof
    rw[] >> simp[extreal_sup_def] >> rw[] >> metis_tac[]
QED

Theorem sup_alt:
    (∀p. sup p = +∞ ⇔ p +∞ ∨ ∀y. ∃x. p (Normal x) ∧ y < x) ∧
    (∀p. sup p = −∞ ⇔ p = ∅ ∨ p = {−∞}) ∧
    (∀p r. sup p = Normal r ⇔ ¬p +∞ ∧ ∀y. (∃x. p x ∧ y < x) ⇔ y < Normal r)
Proof
    rw[] >> eq_tac >> rw[] >> fs[sup_to_bool] >> rw[]
    >- (CCONTR_TAC >> fs[GSYM real_lte] >> last_x_assum (qspec_then `Normal y` assume_tac) >> fs[] >>
        rename [`x ≤ Normal y`] >> Cases_on `x` >> rfs[] >>
        last_x_assum (qspec_then `r` assume_tac) >> rfs[])
    >- (last_x_assum (dxrule_then assume_tac) >> Cases_on `x` >> fs[])
    >- (last_x_assum (qspec_then `real x` assume_tac) >> fs[] >>
        last_x_assum (dxrule_then assume_tac) >> Cases_on `x` >> fs[] >>
        (dxrule_all_then mp_tac) REAL_LTE_TRANS >> simp[])
    >- (Cases_on `p = ∅` >> fs[] >> simp[EXTENSION,IN_APP] >> rw[] >> eq_tac >> rw[] >>
        fs[GSYM MEMBER_NOT_EMPTY,IN_APP] >> first_x_assum (drule_then assume_tac) >> fs[])
    >- (qexists_tac `−∞` >> simp[])
    >- (qexists_tac `−∞` >> simp[le_refl])
    >- (CCONTR_TAC >> fs[] >> last_x_assum (dxrule_then assume_tac) >> Cases_on `x` >> rfs[])
    >- (rename [`z ≠ −∞`,`∀y. p y ⇒ y ≤ ub`] >> eq_tac >> rw[]
        >- (Cases_on `y` >> fs[] >> irule REAL_LTE_TRANS >> Cases_on `x` >> fs[]
            >- (last_x_assum (dxrule_then assume_tac) >> Cases_on `ub` >> fs[]) >>
            rename [`p (Normal b)`,`a < b`] >> qexists_tac `b` >> simp[] >>
            irule REAL_IMP_LE_SUP >> rw[]
            (* >- (qexists_tac `b` >> simp[]) *)
            >- (qexists_tac `real ub` >> rw[] >> last_x_assum (dxrule_then assume_tac) >>
                Cases_on `ub` >> fs[])
            >- (qexists_tac `b` >> simp[]))
        >- (Cases_on `y` >> fs[]
            >- (qexists_tac `z` >> Cases_on `z` >> fs[]) >>
            `∀y. (∃x. (λz. p (Normal z)) x ∧ y < x) ⇔ y < sup (λz. p (Normal z))` by (
                irule REAL_SUP >> rw[]
                >- (qexists_tac `real z` >> last_x_assum (drule_then assume_tac) >>
                    Cases_on `z` >> fs[] >> Cases_on `ub` >> fs[])
                >- (qexists_tac `(real ub) + 1` >> rw[] >> last_x_assum (dxrule_then assume_tac) >>
                    Cases_on `ub` >> fs[])) >>
            pop_assum (assume_tac o GSYM) >> fs[] >> qexists_tac `Normal x` >> simp[]))
    >- (qexists_tac `Normal r` >> rw[] >> CCONTR_TAC >> fs[GSYM extreal_lt_def] >>
        last_x_assum (qspec_then `Normal r` mp_tac) >> simp[lt_refl] >> qexists_tac `y` >> simp[])
    >- (CCONTR_TAC >> fs[] >> qpat_x_assum `∀y. _ ⇔ _` mp_tac >> simp[] >>
        `∃x. x < r` by (qexists_tac `r - 1` >> simp[REAL_LT_SUB_RADD,REAL_LT_ADDR]) >>
        qexists_tac `Normal x` >> rw[real_lte] >> CCONTR_TAC >> rfs[] >>
        rename [`Normal x < y`] >> qpat_x_assum `∀x. _ ∨ _` mp_tac >> simp[] >>
        qexists_tac `y` >> simp[] >> CCONTR_TAC >> fs[])
    >- (simp[sup] >> irule EQ_SYM >> irule SELECT_UNIQUE >> rw[] >> Cases_on `y = r` >> rw[]
        >- (pop_assum (qspec_then `Normal y` assume_tac) >> fs[] >>
            Cases_on `y < r` >> fs[] >> rw[]
            >- (qexists_tac `real x` >> Cases_on `x` >> fs[])
            >- (last_x_assum (qspec_then `Normal z` assume_tac) >> fs[]))
        >- (CCONTR_TAC >> fs[] >> rename [`aub ≠ ub`] >> fs[REAL_NE_LT_TOTAL]
            >- (last_x_assum (qspec_then `Normal aub` assume_tac) >> rfs[] >>
                Cases_on `x` >> fs[] >> last_x_assum (qspec_then `aub` mp_tac) >>
                simp[REAL_LT_REFL] >> qexists_tac `r` >> simp[])
            >- (last_x_assum (qspec_then `ub` assume_tac) >> rfs[] >>
                last_x_assum (qspec_then `Normal ub` mp_tac) >> simp[lt_refl] >>
                qexists_tac `Normal z` >> simp[])))
QED

Theorem leeq_trans:
    ∀x:extreal y z. x ≤ y ∧ y = z ⇒ x ≤ z
Proof
    simp[]
QED

Theorem eqle_trans:
    ∀x:extreal y z. x = y ∧ y ≤ z ⇒ x ≤ z
Proof
    simp[]
QED

Theorem sub_le_sub_imp:
    ∀w x y z. w ≤ x ∧ z ≤ y ⇒ w - y ≤ x - z
Proof
    rw[] >> irule le_trans >> qexists_tac `x - y` >> simp[le_lsub_imp,le_rsub_imp]
QED

Theorem le_lmul_neg_imp:
    ∀x y z. z ≤ 0 ∧ x ≤ y ⇒ z * y ≤ z * x
Proof
    rw[] >> simp[Once $ GSYM le_neg] >> qpat_x_assum `_ ≤ 0` assume_tac >>
    dxrule_then assume_tac $ iffLR $ GSYM le_neg >> fs[neg_0] >>
    dxrule_all_then assume_tac $ le_lmul_imp >> fs[mul_lneg]
QED

Theorem le_rmul_neg_imp:
    ∀x y z. z ≤ 0 ∧ x ≤ y ⇒ y * z ≤ x * z
Proof
    rw[] >> simp[Once $ GSYM le_neg] >> qpat_x_assum `_ ≤ 0` assume_tac >>
    dxrule_then assume_tac $ iffLR $ GSYM le_neg >> fs[neg_0] >>
    dxrule_all_then assume_tac $ le_rmul_imp >> fs[mul_rneg]
QED

Theorem le_mul2:
    ∀x1 x2 y1 y2. 0 ≤ x1 ∧ 0 ≤ y1 ∧ x1 ≤ x2 ∧ y1 ≤ y2 ⇒ x1 * y1 ≤ x2 * y2
Proof
    rw[] >> `0 ≤ x2 ∧ 0 ≤ y2` by (NTAC 2 $ dxrule_all_then assume_tac $ le_trans >> simp[]) >>
    map_every (fn tm => Cases_on tm >> fs[extreal_mul_def]) [`x1`,`x2`,`y1`,`y2`] >>
    rw[] >> simp[REAL_MUL_SIGN,REAL_LE_MUL2]
QED

Theorem le_negl:
    ∀x y. -x ≤ y ⇔ -y ≤ x
Proof
    rw[] >> `-x ≤ - -y ⇔ -y ≤ x` suffices_by simp[] >> simp[le_neg, Excl "neg_neg"]
QED

Theorem le_negr:
    ∀x y. x ≤ -y ⇔ y ≤ -x
Proof
    rw[] >> `- -x ≤ -y ⇔ y ≤ -x` suffices_by simp[] >> simp[le_neg, Excl "neg_neg"]
QED

Theorem le_lmul:
    ∀x y z. 0 < x ⇒ (Normal x * y ≤ Normal x * z ⇔ y ≤ z)
Proof
    rw[] >> Cases_on `y` >> Cases_on `z` >> simp[REAL_LE_LMUL,extreal_mul_def]
QED

Theorem eq_lmul:
    ∀x y z. x ≠ 0 ⇒ (Normal x * y = Normal x * z ⇔ y = z)
Proof
    rw[] >> Cases_on `y` >> Cases_on `z` >> rw[extreal_mul_def,REAL_EQ_LMUL2]
QED

Theorem mul_rinv:
    ∀x:extreal. x ≠ 0 ∧ x ≠ +∞ ∧ x ≠ −∞ ⇒ x * x⁻¹ = 1
Proof
    simp[Once mul_comm,mul_linv]
QED

Theorem mul_rinv_pos:
    ∀x:extreal. 0 < x ∧ x ≠ +∞ ⇒ x * x⁻¹ = 1
Proof
    simp[Once mul_comm,mul_linv_pos]
QED

Theorem abs_exp:
    ∀x:extreal. abs (exp x) = exp x
Proof
    rw[] >> Cases_on `x` >> simp[extreal_exp_def,extreal_abs_def,EXP_POS_LE]
QED

Theorem exp_inj:
    ∀x:extreal y. exp x = exp y ⇔ x = y
Proof
    rw[] >> Cases_on `x` >> Cases_on `y` >> simp[extreal_exp_def,EXP_INJ] >>
    `0:real < exp r` suffices_by simp[REAL_LT_LE] >> simp[EXP_POS_LT]
QED

Theorem exp_mono_le:
    ∀x:extreal y. exp x ≤ exp y ⇔ x ≤ y
Proof
    rw[] >> Cases_on `x` >> Cases_on `y` >> simp[extreal_exp_def,EXP_MONO_LE]
    >- (simp[EXP_POS_LE])
    >- (simp[GSYM real_lt,EXP_POS_LT])
QED

Theorem exp_add:
    ∀x:extreal y. (x ≠ −∞ ∧ y ≠ −∞) ∨ (x ≠ +∞ ∧ y ≠ +∞) ⇒ exp (x + y) = exp x * exp y
Proof
    rw[] >> Cases_on `x` >> Cases_on `y` >> fs[] >>
    rw[extreal_add_def,extreal_exp_def,extreal_mul_def,EXP_ADD] >> fs[EXP_NZ,EXP_POS_LT]
QED

Theorem exp_sum:
    ∀(f:α -> extreal) s. FINITE s ∧ ((∀x. x ∈ s ⇒ f x ≠ −∞) ∨ (∀x. x ∈ s ⇒ f x ≠ +∞)) ⇒
        exp (∑ f s) = ∏ (exp ∘ f) s
Proof
    strip_tac >> simp[Once $ GSYM AND_IMP_INTRO] >> Induct_on `s` >>
    rw[EXTREAL_SUM_IMAGE_THM,EXTREAL_PROD_IMAGE_THM,exp_0] >>
    irule EQ_TRANS >> qexists_tac `exp (f e + ∑ f (s DELETE e))` >> simp[exp_inj] >>
    irule_at Any EXTREAL_SUM_IMAGE_PROPERTY >> simp[DELETE_NON_ELEMENT_RWT] >>
    irule_at Any EQ_TRANS >> qexists_tac `exp (f e) * exp(∑ f s)` >>
    irule_at Any exp_add >> simp[EXTREAL_SUM_IMAGE_NOT_INFTY]
    >| [DISJ1_TAC,DISJ2_TAC] >> rw[] >> simp[]
QED

Theorem EXTREAL_SUM_IMAGE_ALT_FOLDR:
    ∀f s. FINITE s ⇒ ∑ f s = FOLDR (λe acc. f e + acc) 0x (REV_CHOICE_LIST s)
Proof
    simp[EXTREAL_SUM_IMAGE_DEF,ITSET_TO_FOLDR]
QED

Theorem EXTREAL_SUM_IMAGE_EQ':
    ∀f g s. FINITE s ∧ (∀x. x ∈ s ⇒ f x = g x) ⇒ ∑ f s = ∑ g s: extreal
Proof
    rw[] >> simp[EXTREAL_SUM_IMAGE_ALT_FOLDR] >> irule FOLDR_CONG >>
    rw[] >> rfs[REV_CHOICE_LIST_ALT]
QED

Theorem EXTREAL_SUM_IMAGE_MONO':
    ∀f g s. FINITE s ∧ (∀x. x ∈ s ⇒ f x ≤ g x) ⇒ ∑ f s ≤ ∑ g s: extreal
Proof
    `∀f g l. (∀e. MEM e l ⇒ f e ≤ g e) ⇒
      (FOLDR (λe acc. f e + acc) 0x l ≤ FOLDR (λe acc. g e + acc) 0x l)` suffices_by (
        rw[EXTREAL_SUM_IMAGE_ALT_FOLDR] >> last_x_assum irule >> simp[REV_CHOICE_LIST_ALT]) >>
    Induct_on `l` >> rw[FOLDR] >> irule le_add2 >> simp[]
QED

Theorem EXTREAL_SUM_IMAGE_COUNT_0:
    ∀f. ∑ f (count 0) = 0:extreal
Proof
    rw[] >> fs[EXTREAL_SUM_IMAGE_DEF,ITSET_EMPTY]
QED

Theorem EXTREAL_SUM_IMAGE_COUNT_ONE:
    ∀f. ∑ f (count 1) = f 0:extreal
Proof
    rw[] >> `count 1 = {0}` by fs[count_def,EXTENSION] >>
    fs[EXTREAL_SUM_IMAGE_DEF,ITSET_SING,add_rzero]
QED

Theorem EXTREAL_SUM_IMAGE_COUNT_SUC:
    ∀f n. (∀m. m ≤ n ⇒ f m ≠ −∞) ∨ (∀m. m ≤ n ⇒ f m ≠ +∞) ⇒
        ∑ f (count (SUC n)) = (∑ f (count n)) + f n:extreal
Proof
    rw[] >> `count (SUC n) = (count n) ∪ {n}` by fs[count_def,EXTENSION] >>
    rw[] >> pop_assum kall_tac >>
    `∑ f (count n ∪ {n}) = ∑ f (count n) + ∑ f {n}` suffices_by fs[EXTREAL_SUM_IMAGE_SING] >>
    irule EXTREAL_SUM_IMAGE_DISJOINT_UNION >> simp[]
QED

Theorem EXTREAL_PROD_IMAGE_NOT_INFTY:
    ∀f s. FINITE s ∧ (∀x. x ∈ s ⇒ f x ≠ −∞ ∧ f x ≠ +∞) ⇒ ∏ f s ≠ −∞ ∧ ∏ f s ≠ +∞
Proof
    strip_tac >> simp[Once $ GSYM AND_IMP_INTRO] >> Induct_on `s` >> CONJ_TAC
    >- simp[EXTREAL_PROD_IMAGE_EMPTY,SYM normal_1] >>
    NTAC 5 strip_tac >> fs[EXTREAL_PROD_IMAGE_PROPERTY,DELETE_NON_ELEMENT_RWT] >>
    Cases_on `f e` >> Cases_on `∏ f s` >> rfs[extreal_mul_def]
QED

Theorem EXTREAL_PROD_IMAGE_NORMAL:
    ∀f s. FINITE s ⇒ ∏ (λx. Normal (f x)) s = Normal (∏ f s)
Proof
    strip_tac >> Induct_on `s` >>
    rw[EXTREAL_PROD_IMAGE_THM,REAL_PROD_IMAGE_THM,DELETE_NON_ELEMENT_RWT,extreal_mul_def,normal_1]
QED

Theorem EXTREAL_PROD_IMAGE_ONE:
    ∀s. FINITE s ⇒ ∏ (λx. 1) s = 1x
Proof
    Induct_on `s` >> simp[EXTREAL_PROD_IMAGE_EMPTY,EXTREAL_PROD_IMAGE_PROPERTY,DELETE_NON_ELEMENT_RWT]
QED

Theorem EXTREAL_PROD_IMAGE_POS:
    ∀f s. FINITE s ∧ (∀x. x ∈ s ⇒ 0 ≤ f x) ⇒ 0 ≤ ∏ f s
Proof
    strip_tac >> simp[GSYM AND_IMP_INTRO] >> Induct_on `s` >>
    rw[EXTREAL_PROD_IMAGE_THM,DELETE_NON_ELEMENT_RWT] >> irule le_mul >> simp[]
QED

Theorem EXTREAL_PROD_IMAGE_LE:
    ∀f g s. FINITE s ∧ (∀x. x ∈ s ⇒ 0 ≤ f x ∧ f x ≤ g x) ⇒ ∏ f s ≤ ∏ g s
Proof
    NTAC 2 strip_tac >> simp[GSYM AND_IMP_INTRO] >> Induct_on `s` >>
    rw[EXTREAL_PROD_IMAGE_THM,DELETE_NON_ELEMENT_RWT] >> irule le_mul2 >>
    simp[EXTREAL_PROD_IMAGE_POS]
QED

Theorem EXTREAL_PROD_IMAGE_COUNT_SUC:
    ∀f n. ∏ f (count (SUC n)) = ∏ f (count n) * f n: extreal
Proof
    rw[] >> qspecl_then [`f`,`n`,`count n`] assume_tac EXTREAL_PROD_IMAGE_PROPERTY >>
    rfs[] >> simp[mul_comm] >> pop_assum $ SUBST1_TAC o SYM >>
    `count (SUC n) = n INSERT count n` suffices_by simp[] >> simp[EXTENSION]
QED

Theorem EXTREAL_PROD_IMAGE_EQ_INTER:
    ∀s t f g. FINITE s ∧ FINITE t ∧ (∀x. x ∈ s ∧ x ∈ t ⇒ f x = g x) ∧
        (∀x. x ∈ s ∧ x ∉ t ⇒ f x = 1) ∧ (∀x. x ∉ s ∧ x ∈ t ⇒ g x = 1) ⇒
        ∏ f s = ∏ g t
Proof
    rw[] >>
    map_every (fn (th,ql,thl) => qspecl_then ql mp_tac th >> simp thl >> DISCH_THEN kall_tac) [
        (EXTREAL_PROD_IMAGE_DISJOINT_UNION,[`s ∩ t`,`s DIFF t`],[UNION_INTER_DIFF,DISJOINT_INTER_DIFF]),
        (EXTREAL_PROD_IMAGE_DISJOINT_UNION,[`t ∩ s`,`t DIFF s`],[UNION_INTER_DIFF,DISJOINT_INTER_DIFF]),
        (EXTREAL_PROD_IMAGE_EQ,[`s DIFF t`,`f`,`λx. 1`],[EXTREAL_PROD_IMAGE_ONE]),
        (EXTREAL_PROD_IMAGE_EQ,[`t DIFF s`,`g`,`λx. 1`],[EXTREAL_PROD_IMAGE_ONE])] >>
    simp[Once INTER_COMM] >> irule EXTREAL_PROD_IMAGE_EQ >> simp[]
QED

Theorem ext_suminf_sing_general:
    ∀m r. 0 ≤ r ⇒ suminf (λn. if n = m then r else 0) = r
Proof
    rw[] >> `∀n. 0 ≤ (λn. if n = m then r else 0) n` by rw[] >> fs[ext_suminf_def] >>
    `(λn. ∑ (λn. if n = m then r else 0) (count n)) = (λn. if n < SUC m then 0 else r)` by (
        rw[FUN_EQ_THM] >> Induct_on `n` >- simp[EXTREAL_SUM_IMAGE_COUNT_0] >> simp[] >>
        (qspecl_then [`(λn. if n = m then r else 0)`,`n`] assume_tac) EXTREAL_SUM_IMAGE_COUNT_SUC >>
        rfs[pos_not_neginf] >> pop_assum kall_tac >>
        map_every (fn tm => Cases_on tm >> simp[]) [`n < m`,`n = m`]) >>
    simp[] >> pop_assum kall_tac >> rw[IMAGE_DEF,sup_eq] >- rw[] >>
    pop_assum irule >> qexists_tac `SUC m` >> simp[]
QED

Theorem ext_suminf_nested:
    ∀f. (∀m n. 0 ≤ f m n) ⇒ suminf (λn. suminf (λm. f m n)) = suminf (λm. suminf (λn. f m n))
Proof
    rw[] >>
    map_every (fn tms => qspecl_then tms assume_tac ext_suminf_2d_full)
        [[`λm n. f m n`,`(λm. suminf (λn. f m n))`,`num_to_pair`],
        [`λn m. f m n`,`(λn. suminf (λm. f m n))`,`SWAP ∘ num_to_pair`]] >>
    rfs[BIJ_NUM_TO_PAIR,INST_TYPE [alpha |-> ``:num``,beta |-> ``:num``] BIJ_SWAP,BIJ_COMPOSE,SF SFY_ss] >>
    NTAC 2 $ pop_assum $ SUBST1_TAC o SYM >> irule ext_suminf_eq >> rw[o_DEF] >>
    Cases_on `num_to_pair n` >> simp[SWAP_def]
QED

Theorem ext_suminf_first:
    ∀f. (∀n. 0 ≤ f n) ⇒ suminf f = f 0 + suminf (f ∘ SUC)
Proof
    rw[] >>
    qspecl_then [`(λn. if n = 0 then f 0 else 0)`,
        `(λn. if 0 < n then f n else 0)`] assume_tac ext_suminf_add >> rfs[ext_suminf_sing] >>
    `(λn. (if n = 0 then f 0 else 0) + if 0 < n then f n else 0) = f` by (
        rw[FUN_EQ_THM] >> Cases_on `n` >> simp[]) >>
    fs[] >> pop_assum kall_tac >>
    `suminf f = f 0 + suminf (λn. if 0 < n then f n else 0)` by (pop_assum irule >> rw[]) >>
    simp[] >> NTAC 2 $ pop_assum kall_tac >> irule IRULER >>
    qspec_then `λm n. if SUC m = n then f n else 0` assume_tac ext_suminf_nested >>
    `suminf (λn. suminf (λm. (λm n. if SUC m = n then f n else 0) m n)) =
        suminf (λn. if 0 < n then f n else 0)` by (
        irule ext_suminf_eq >> rw[ext_suminf_0] >> Cases_on `n` >> fs[ext_suminf_sing_general]) >>
    `suminf (λm. suminf (λn. (λm n. if SUC m = n then f n else 0) m n)) = suminf (f ∘ SUC)` by (
        irule ext_suminf_eq >> qx_gen_tac `m` >> simp[o_DEF] >>
        last_x_assum $ qspec_then `SUC m` assume_tac >> dxrule_then assume_tac ext_suminf_sing_general >>
        pop_assum $ qspec_then `SUC m` (SUBST1_TAC o SYM) >> irule ext_suminf_eq >>
        gen_tac >> simp[] >> Cases_on `SUC m = n` >> simp[]) >>
    fs[] >> NTAC 2 $ pop_assum kall_tac >> pop_assum irule >> rw[]
QED

Theorem ext_suminf_sigma_gen:
    ∀f s. FINITE s ∧ (∀i j. i ∈ s ⇒ 0 ≤ f i j) ⇒
        ∑ (λi. suminf (f i)) s = suminf (λj. ∑ (λi. f i j) s)
Proof
    rw[] >> drule_then assume_tac FINITE_BIJ_COUNT >> fs[] >> rename [`BIJ g (count n) _`] >>
    drule_then assume_tac BIJ_IMAGE >> fs[] >> rw[] >>
    `∀i j. i < n ⇒ 0 ≤ (f ∘ g) i j` by (rw[] >> last_x_assum irule >> qexists_tac `i` >> simp[]) >>
    last_x_assum kall_tac >>
    `∀h. (∀k. k < n ⇒ 0 ≤ (h ∘ g) k) ⇒ ∑ h (IMAGE g (count n)) = ∑ (h ∘ g) (count n)` by (rw[] >>
        qspecl_then [`count n`,`g`,`h`] assume_tac $
            SIMP_RULE (srw_ss ()) [GSYM RIGHT_FORALL_IMP_THM] EXTREAL_SUM_IMAGE_IMAGE >>
        rfs[iffLR BIJ_DEF] >> pop_assum irule >> DISJ1_TAC >> rw[] >>
        irule pos_not_neginf >> simp[]) >>
    qspecl_then [`f ∘ g`,`n`] (assume_tac o SIMP_RULE (srw_ss ()) []) ext_suminf_sigma' >> rfs[] >>
    simp[o_DEF] >> pop_assum $ SUBST1_TAC o SYM >>
    pop_assum $ qspec_then `(λi. suminf (f i))` assume_tac >> rfs[o_DEF] >> pop_assum irule >>
    rw[] >> irule ext_suminf_pos >> simp[]
QED

Theorem ext_suminf_le:
    ∀f c. (∀n. 0 ≤ f n) ⇒ (suminf f ≤ c ⇔ ∀n. (∑ f (count n)) ≤ c)
Proof
    rw[SIMP_RULE (srw_ss ()) [o_DEF] $ SIMP_RULE (srw_ss ()) [GSYM o_DEF,GSYM I_EQ_IDABS] ext_suminf_alt,sup_le] >>
    eq_tac >> rw[] >> simp[] >> pop_assum irule >> qexists_tac `n` >> simp[]
QED

Theorem ext_le_suminf:
    ∀f c. (∀n. 0 ≤ f n) ⇒ (c ≤ suminf f ⇔ ∀z. (∀n. ∑ f (count n) ≤ z) ⇒ c ≤ z)
Proof
    rw[SIMP_RULE (srw_ss ()) [o_DEF] $ SIMP_RULE (srw_ss ()) [GSYM o_DEF,GSYM I_EQ_IDABS] ext_suminf_alt,le_sup] >>
    eq_tac >> rw[] >> simp[] >> last_x_assum irule >> rw[] >> simp[] >>
    pop_assum irule >> qexists_tac `n` >> simp[]
QED

Theorem infty_greatest:
    ∀x. x = +∞ ⇔ ∀y. y ≤ x
Proof
    rw[] >> eq_tac >> rw[] >>
    pop_assum (qspec_then `+∞` assume_tac) >> Cases_on `x` >> fs[]
QED

Theorem closed_interval_mul:
    ∀a b c d x y. a ≤ x ∧ x ≤ b ∧ c ≤ y ∧ y ≤ d ⇒
        -max (abs a) (abs b) * max (abs c) (abs d) ≤ x * y ∧
        x * y ≤ max (abs a) (abs b) * max (abs c) (abs d)
Proof
    simp[mul_lneg,GSYM abs_bounds] >> rw[] >>
    simp[abs_mul] >> irule le_mul2 >> simp[abs_pos,le_max] >>
    simp[abs_bounds,le_negl,le_abs_bounds,GSYM DISJ_ASSOC] >>
    `(a ≤ -x ∨ -x ≤ b) ∧ (c ≤ -y ∨ -y ≤ d)` suffices_by (rw[] >> fs[le_negl]) >>
    `(x ≤ -x ∨ -x ≤ x) ∧ (y ≤ -y ∨ -y ≤ y)` by simp[le_total] >>
    NTAC 2 $ dxrule_all_then assume_tac $ le_trans >> simp[]
QED

Theorem sup_add:
    ∀p q. (sup p ≠ −∞ ∧ sup q ≠ −∞) ∨ (sup p ≠ +∞ ∧ sup q ≠ +∞) ⇒
        sup p + sup q = sup {x + y | p x ∧ q y}
Proof
    rpt GEN_TAC >>
    Cases_on `sup p` >> Cases_on `sup q` >> simp[extreal_add_def] >>
    fs[sup_to_bool] >> rw[]
    >- (qexists_tac `x + x'` >> rename[`x + y ≠ +∞`] >> REVERSE (rw[])
        >- (Cases_on `x` >> Cases_on `y` >> fs[extreal_add_def]) >>
        rename [`(z,T) = _ xy`] >> Cases_on `xy` >> rename [`_ = _ (a,b)`] >> fs[extreal_add_def])
    >- (rename [`(z,T) = _ xy`] >> Cases_on `xy` >> rename [`_ = _ (a,b)`] >> fs[extreal_add_def])
    >- (qexists_tac `x + x'` >> rename[`x + y ≠ +∞`] >> REVERSE (rw[])
        >- (Cases_on `x` >> Cases_on `y` >> fs[extreal_add_def]) >>
        rename [`(z,T) = _ xy`] >> Cases_on `xy` >> rename [`_ = _ (a,b)`] >>
        fs[] >> irule le_add2 >> fs[])
    >- (rename [`(z,T) = _ xy`] >> Cases_on `xy` >> rename [`_ = _ (a,b)`] >>
        fs[] >> Cases_on `b` >> fs[extreal_add_def] >> first_x_assum (dxrule_then assume_tac) >>
        rename [`+∞ ≤ y`] >> Cases_on `y` >> fs[])
    >- (NTAC 2 (last_x_assum (qspec_then `x / 2` assume_tac)) >> CCONTR_TAC >>
        `x / 2 ≠ +∞` by (
            assume_tac (EVAL ``2 = Normal 2``) >> fs[] >>
            Cases_on `x` >> fs[extreal_div_def,extreal_inv_def,extreal_mul_def]) >>
        fs[GSYM extreal_lt_def] >>
        last_x_assum (qspec_then `y + y'` assume_tac) >> rename [`x + y ≤ z`] >>
        `x + y ≤ z` by (pop_assum irule >> qexists_tac `(x,y)` >> simp[]) >>
        (qspecl_then [`z / 2`,`x`,`z / 2`,`y`] assume_tac) lt_add2 >> rfs[] >>
        `z / 2 + z / 2 < z` by (irule lte_trans >> qexists_tac `x + y` >> fs[]) >>
        `z / 2 + z / 2 = z` suffices_by (rw[] >> CCONTR_TAC >> fs[]) >>
        rpt (pop_assum kall_tac) >> simp[EVAL ``z / 2 + z / 2 = z``] >>
        Cases_on `z` >> fs[extreal_div_def,extreal_inv_def,extreal_mul_def,extreal_add_def] >>
        (qspec_then `r` assume_tac) REAL_HALF_DOUBLE >>
        fs[Once real_div] >> fs[Once REAL_ADD_COMM] >> fs[Once real_div])
    >- (rename [`z = +∞`,`q y`,`y ≠ −∞`] >> first_x_assum (drule_then assume_tac) >>
        last_x_assum (qspec_then `z - y` assume_tac) >> CCONTR_TAC >>
        `∃yr. y = Normal yr` by (Cases_on `y` >> fs[] >> Cases_on `x` >> fs[]) >> rw[] >>
        `z − Normal yr ≠ +∞` by (Cases_on `z` >> fs[extreal_sub_def]) >> fs[GSYM extreal_lt_def] >>
        last_x_assum (qspec_then `y + Normal yr` assume_tac) >>
        `y + Normal yr ≤ z` by (pop_assum irule >> qexists_tac `(y,Normal yr)` >> simp[]) >>
        fs[] >> rw[] >> (qspecl_then [`Normal yr`,`z`,`y`] assume_tac) sub_lt_eq >> fs[] >>
        (dxrule_all_then assume_tac) lte_trans >> fs[])
    >- (rename [`∀y. p y ⇒ y ≤ pub`,`p pel`,`∀y. q y ⇒ y ≤ qub`] >> fs[] >>
        qexists_tac `pub + qub` >> REVERSE (rw[])
        >- (Cases_on `pub` >> Cases_on `qub` >> fs[extreal_add_def]) >>
        rename [`(z,T) = _ xy`] >> Cases_on `xy` >> rename [`_ = _ (a,b)`] >> fs[] >>
        irule le_add2 >> fs[])
    >- (rename [`∀y. p y ⇒ y ≤ pub`,`p pel`,`∀y. q y ⇒ y ≤ qub`] >> fs[] >>
        rename [`(z,T) = _ xy`] >> Cases_on `xy` >> rename [`_ = _ (a,b)`] >> fs[] >>
        last_x_assum (dxrule_then assume_tac) >> Cases_on `a` >> fs[extreal_add_def] >>
        Cases_on `pub` >> fs[])
    >- (rename [`z = +∞`,`p y`,`y ≠ −∞`] >> first_x_assum (drule_then assume_tac) >>
        last_x_assum (qspec_then `z - y` assume_tac) >> CCONTR_TAC >>
        `∃yr. y = Normal yr` by (Cases_on `y` >> fs[] >> Cases_on `x` >> fs[]) >> rw[] >>
        `z − Normal yr ≠ +∞` by (Cases_on `z` >> fs[extreal_sub_def]) >> fs[GSYM extreal_lt_def] >>
        last_x_assum (qspec_then `Normal yr + y` assume_tac) >>
        `Normal yr + y ≤ z` by (pop_assum irule >> qexists_tac `(Normal yr,y)` >> simp[]) >>
        fs[] >> rw[] >> (qspecl_then [`Normal yr`,`z`,`y`] assume_tac) sub_lt_eq >> fs[] >>
        `y + Normal yr = Normal yr + y` suffices_by (simp[] >> CCONTR_TAC >> fs[] >>
            (dxrule_all_then assume_tac) lte_trans >> fs[]) >>
        irule add_comm >> simp[] >> DISJ1_TAC >> CCONTR_TAC >> fs[extreal_add_def])
    >- (qexists_tac `x + x''` >>
        rename [`pub + qub`,`∀y. p y ⇒ y ≤ pub`,`∀y. q y ⇒ y ≤ qub`,`p pel`,`q qel`] >> REVERSE (rw[])
        >- (Cases_on `pub` >> Cases_on `qub` >> fs[extreal_add_def]) >>
        rename [`(z,T) = _ xy`] >> Cases_on `xy` >> rename [`_ = _ (a,b)`] >> fs[] >>
        irule le_add2 >> fs[])
    >- (rename [`y ≠ −∞`] >> qexists_tac `x' + y` >>
        rename [`pel + qel`,`p pel`,`q qel`,`∀y. p y ⇒ y ≤ pub`,`∀y. q y ⇒ y ≤ qub`] >> REVERSE (rw[])
        >- (Cases_on `pel` >> Cases_on `qel` >> fs[extreal_add_def]) >>
        qexists_tac `(pel,qel)` >> simp[])
    >- (rename [`sup (λz. p (Normal z)) + sup (λz. q (Normal z))`,
            `∀y. p y ⇒ y ≤ pub`,`p pel`,`∀y. q y ⇒ y ≤ qub`,`q qel`] >>
        map_every qabbrev_tac [`pN = (λz. p (Normal z))`,`qN = (λz. q (Normal z))`] >>
        `sup pN + sup qN = sup {x + y | pN x ∧ qN y}` by (
            irule REAL_SUP_ADD >> rw[] >> map_every qunabbrev_tac [`pN`,`qN`] >> fs[]
            >- (qexists_tac `real pel` >> Cases_on `pel` >> fs[] >>
                NTAC 2 (last_x_assum (dxrule_then assume_tac)) >> Cases_on `pub` >> fs[])
            >- (qexists_tac `real qel` >> Cases_on `qel` >> fs[] >>
                NTAC 2 (last_x_assum (dxrule_then assume_tac)) >> Cases_on `qub` >> fs[])
            >- (qexists_tac `real pub` >> rw[] >> NTAC 3 (last_assum (dxrule_then assume_tac)) >>
                Cases_on `pub` >> fs[])
            >- (qexists_tac `real qub` >> rw[] >> NTAC 3 (last_assum (dxrule_then assume_tac)) >>
                Cases_on `qub` >> fs[])) >>
        fs[] >> map_every qunabbrev_tac [`pN`,`qN`] >> fs[] >> irule IRULER >>
        rw[EXTENSION] >> eq_tac >> rw[]
        >- (rename [`Normal (x + y)`] >> qexists_tac `(Normal x,Normal y)` >> simp[extreal_add_def])
        >- (rename [`(Normal z,T) = _ xy`] >> Cases_on `xy` >> rename [`_ = _ (a,b)`] >> fs[] >>
            map_every qexists_tac [`real a`,`real b`] >>
            Cases_on `a` >> Cases_on `b` >> fs[extreal_add_def,real_normal] >>
            NTAC 2 (last_x_assum (dxrule_then assume_tac)) >> rename [`+∞ ≤ ub`] >>
            Cases_on `ub` >> fs[]))
QED

Theorem sup_cmul_alt_real:
    ∀p c. 0 ≤ c ∧ (c = 0 ⇒ ∃e. p e) ⇒ Normal c * sup p = sup {Normal c * x | p x}
Proof
    rw[] >> REVERSE (fs[REAL_LE_LT])
    >- (rfs[] >> simp[normal_0] >> `{0 | x | p x} = {0}` suffices_by rw[sup_sing] >>
        rw[EXTENSION,IN_APP] >> eq_tac >> rw[] >> qexists_tac `e` >> simp[]) >>
    pop_assum kall_tac >> Cases_on `sup p` >> simp[extreal_mul_def] >> fs[sup_alt] >> rw[]
    >- (DISJ2_TAC >> rw[EXTENSION,extreal_mul_def])
    >- (DISJ1_TAC >> qexists_tac `+∞` >> rw[EXTENSION,extreal_mul_def])
    >- (DISJ2_TAC >> rw[] >> last_x_assum (qspec_then `c⁻¹ * y` assume_tac) >> fs[] >>
        qexists_tac `c * x` >> (qspecl_then [`c`,`c⁻¹ * y`,`x`] assume_tac) (GSYM REAL_LT_LMUL) >>
        rfs[REAL_MUL_ASSOC,REAL_MUL_RINV,REAL_POS_NZ] >> pop_assum kall_tac >>
        qexists_tac `Normal x` >> simp[extreal_mul_def])
    >- (Cases_on `x` >> rfs[extreal_mul_def])
    >- (rename [`y < Normal (c * ub)`] >> last_x_assum (qspec_then `Normal c⁻¹ * y` (assume_tac o GSYM)) >>
        `∀x. Normal c⁻¹ * y < x ⇔ y < Normal c * x` by (rw[] >>
            (qspecl_then [`Normal c`,`Normal c⁻¹ * y`,`x`] assume_tac) (GSYM lt_lmul) >>
            rfs[GSYM normal_0,extreal_lt_simp,mul_assoc,extreal_mul_def,REAL_MUL_RINV,REAL_POS_NZ,normal_1]) >>
        fs[extreal_mul_def] >> NTAC 2 (pop_assum kall_tac) >> eq_tac >> rw[] >> rename [`Normal c * x`]
        >| [qexists_tac `x`,qexists_tac `Normal c * x`] >> simp[] >> qexists_tac `x` >> simp[])
QED

Theorem sup_cmul_alt_real_loose:
    ∀p c. 0 ≤ c ∧ (∃e. p e) ⇒ Normal c * sup p = sup {Normal c * x | p x}
Proof
    rw[sup_cmul_alt_real]
QED

Theorem sup_cmul_alt_ext:
    ∀p c. 0 ≤ c ∧ (c = 0 ⇒ ∃e. p e) ∧ (c = +∞ ⇒ ∃e. 0 ≤ e ∧ p e) ⇒ c * sup p = sup {c * x | p x}
Proof
    rw[] >> Cases_on `c` >> fs[sup_cmul_alt_real] >> rw[] >>
    Cases_on `sup p` >> simp[extreal_mul_def] >> rw[] >> fs[sup_alt] >> rw[]
    >- (fs[])
    >- (DISJ1_TAC >> qexists_tac `+∞` >> simp[extreal_mul_def])
    >- (DISJ1_TAC >> pop_assum $ qspec_then `0` assume_tac >>
        fs[] >> qexists_tac `Normal x` >> simp[extreal_mul_def])
    >- (Cases_on `x` >> fs[extreal_mul_def] >> pop_assum mp_tac >> rw[] >>
        dxrule_then assume_tac REAL_MEAN >> fs[] >> first_x_assum $ qspec_then `Normal z` assume_tac >>
        rfs[] >> first_x_assum $ qspec_then `Normal r` assume_tac >> rfs[])
    >- (`∀x. p x ⇒ x ≤ 0` by (rw[] >> first_x_assum $ qspec_then `Normal 0` assume_tac >>
            fs[] >> first_x_assum $ qspec_then `x` assume_tac >> rfs[normal_0,extreal_not_lt]) >>
        first_assum $ drule_then assume_tac >> dxrule_all_then assume_tac $ iffLR le_antisym >>
        gvs[normal_0] >> Cases_on `y < 0` >> simp[] >- (NTAC 2 $ (qexists_tac `0` >> simp[])) >>
        rw[] >> simp[DISJ_COMM,DISJ_EQ_IMP] >> rw[] >> rename [`¬p x`] >> CCONTR_TAC >> fs[] >>
        qpat_x_assum `¬(y < 0)` mp_tac >> simp[] >> irule lte_trans >> qexists_tac `+∞ * x` >>
        simp[] >> first_x_assum $ dxrule_then assume_tac >> irule mul_le >> simp[])
    >- (DISJ1_TAC >> first_x_assum $ qspec_then `Normal 0` assume_tac >> rfs[] >>
        qexists_tac `x` >> Cases_on `x` >> fs[extreal_mul_def])
    >- (Cases_on `{+∞ * x | p x} = ∅` >> fs[] >> fs[GSYM MEMBER_NOT_EMPTY] >>
        pop_assum mp_tac >> rename [`p e ⇒ _`] >> rw[EXTENSION] >>
        `∀x. p x ⇒ x < 0` by (
            rw[] >> fs[REAL_NE_LT_TOTAL] >> dxrule_then assume_tac REAL_MEAN >> fs[] >>
            first_x_assum $ qspec_then `Normal z` assume_tac >> rfs[] >>
            first_x_assum $ qspec_then `x` assume_tac >> rfs[extreal_not_lt] >>
            irule let_trans >> qexists_tac `Normal z` >> simp[]) >>
        eq_tac >> rw[] >| [all_tac,qexists_tac `e` >> simp[]] >> rename [`+∞ * x = −∞`] >>
        first_x_assum $ dxrule_then assume_tac >> Cases_on `x` >> fs[extreal_mul_def])
QED

Theorem sup_cmul_alt_ext_loose:
    ∀p c. 0 ≤ c ∧ (∃e. 0 ≤ e ∧ p e) ⇒ c * sup p = sup {c * x | p x}
Proof
    rw[] >> irule sup_cmul_alt_ext >> rw[] >> qexists_tac `e` >> simp[]
QED

(*---------------------------------------------------------------------------*)
(* Trivial stuff for Sigma Algebras *)
(*---------------------------------------------------------------------------*)

Theorem SIGMA_ALGEBRA_SUBSET_SPACE:
    ∀sa A. sigma_algebra sa ∧ A ∈ subsets sa ⇒ A ⊆ space sa
Proof
    rw[sigma_algebra_def,algebra_def,subset_class_def]
QED

Theorem SUBSET_PROD_SETS:
    ∀a b c d. a ⊆ c ∧ b ⊆ d ⇒ prod_sets a b ⊆ prod_sets c d
Proof
    rw[prod_sets_def,SUBSET_DEF] >> qexistsl_tac [`t`,`u`] >> simp[]
QED

Theorem SIGMA_ALGEBRA_PROD_SIGMA_WEAK:
    ∀a b. sigma_algebra a ∧ sigma_algebra b ⇒ sigma_algebra (a × b)
Proof
    rw[] >> irule SIGMA_ALGEBRA_PROD_SIGMA >> fs[sigma_algebra_def,algebra_def]
QED

Theorem IN_SPACE_PROD_SIGMA:
    ∀a b z. z ∈ space (a × b) ⇔ FST z ∈ space a ∧ SND z ∈ space b
Proof
    rw[prod_sigma_def,SPACE_SIGMA]
QED

Theorem SUBSETS_PROD_SIGMA:
    ∀a b. subsets (a × b) =
        BIGINTER {s | prod_sets (subsets a) (subsets b) ⊆ s ∧ sigma_algebra (space a × space b,s)}
Proof
    simp[prod_sigma_def,sigma_def]
QED

Theorem SIGMA_ALGEBRA_SUBSET_CLASS:
    ∀a. sigma_algebra a ⇒ subset_class (space a) (subsets a)
Proof
    simp[SIGMA_ALGEBRA]
QED

Theorem SUBSET_CLASS_PROD_SETS:
    ∀spa stsa spb stsb. subset_class spa stsa ∧ subset_class spb stsb ⇒
        subset_class (spa × spb) (prod_sets stsa stsb)
Proof
    rw[subset_class_def,FORALL_PROD] >> irule SUBSET_CROSS >> simp[]
QED

Theorem SUBSET_CLASS_ANTIMONO:
    ∀sp a b. ¬subset_class sp a ∧ a ⊆ b ⇒ ¬subset_class sp b
Proof
    rw[subset_class_def] >> qexists_tac `x` >> simp[] >> fs[SUBSET_DEF]
QED

Theorem SIGMA_EXPLODE:
    ∀sp sts. ¬subset_class sp sts ⇒ sigma sp sts = (sp,UNIV)
Proof
    rw[sigma_def] >> `{s | sts ⊆ s ∧ sigma_algebra (sp,s)} = ∅` suffices_by simp[BIGINTER_EMPTY] >>
    simp[EXTENSION] >> qx_gen_tac `s` >> Cases_on `sts ⊆ s` >> simp[] >>
    dxrule_then assume_tac SUBSET_CLASS_ANTIMONO >> pop_assum $ dxrule_then assume_tac >>
    simp[sigma_algebra_def,algebra_def]
QED

Theorem SIGMA_ALGEBRA_ALT_DIFF:
    ∀a. sigma_algebra a ⇔ subset_class (space a) (subsets a) ∧ space a ∈ subsets a ∧
        (∀s t. s ∈ subsets a ∧ t ∈ subsets a ⇒ t DIFF s ∈ subsets a) ∧
        ∀c. countable c ∧ c ⊆ subsets a ⇒ BIGUNION c ∈ subsets a
Proof
    rw[] >> eq_tac >- simp[iffLR SIGMA_ALGEBRA,SIGMA_ALGEBRA_SPACE,SIGMA_ALGEBRA_DIFF] >>
    rw[] >> simp[SIGMA_ALGEBRA] >> `space a DIFF space a ∈ subsets a` by simp[] >>
    pop_assum mp_tac >> SIMP_TAC bool_ss [DIFF_EQ_EMPTY]
QED

Theorem SIGMA_SIGMA:
    ∀sp sts. sigma sp (subsets (sigma sp sts)) = sigma sp sts
Proof
    rw[] >> irule SIGMA_CONG >> irule SUBSET_ANTISYM >> simp[SIGMA_SUBSET_SUBSETS] >>
    REVERSE $ Cases_on `subset_class sp sts`
    >- (qspecl_then [`sp`,`sts`,`UNIV`] assume_tac SUBSET_CLASS_ANTIMONO >>
        rfs[SUBSET_UNIV] >> simp[SIGMA_EXPLODE]) >>
    irule SIGMA_PROPERTY_DISJOINT_LEMMA >> dxrule_then assume_tac SIGMA_ALGEBRA_SIGMA >>
    simp[SUBSET_REFL,SIGMA_REDUCE,SIGMA_ALGEBRA_ALGEBRA,SIGMA_ALGEBRA_IMP_DYNKIN_SYSTEM]
QED

Theorem SIGMA_BOUNDED:
    ∀sp a b. a ⊆ subsets (sigma sp b) ⇒ subsets (sigma sp a) ⊆ subsets (sigma sp b)
Proof
    rw[] >> dxrule_then assume_tac SIGMA_MONOTONE >>
    pop_assum $ qspec_then `sp` mp_tac >> simp[SIGMA_SIGMA]
QED

Theorem SIGMA_PROPERTY_WEAK:
    ∀sp sts P. sts ⊆ P ∧ sigma_algebra (sp,P) ⇒ subsets (sigma sp sts) ⊆ P
Proof
    rw[sigma_def] >> simp[Once SUBSET_DEF]
QED

Theorem SIGMA_PROPERTY_WEAK_ALT:
    ∀sp sts P x. sts ⊆ P ∧ sigma_algebra (sp,P) ∧ x ∈ subsets (sigma sp sts) ⇒ x ∈ P
Proof
    rw[] >> dxrule_then mp_tac SIGMA_PROPERTY_WEAK >> simp[SUBSET_DEF,SF SFY_ss]
QED

Theorem IMAGE_SIGMA_ALGEBRA:
    ∀A sp f. sigma_algebra A ∧ BIJ f (space A) sp ⇒ sigma_algebra (sp,IMAGE (IMAGE f) (subsets A))
Proof
    rw[] >> rw[SIGMA_ALGEBRA_ALT_SPACE,subset_class_def]
    >- (rename [`IMAGE f s`] >> simp[SUBSET_DEF] >>
        dxrule_all_then mp_tac SIGMA_ALGEBRA_SUBSET_SPACE >> rw[SUBSET_DEF] >>
        rename [`f x ∈ sp`] >> fs[BIJ_ALT,FUNSET])
    >- (qexists_tac `space A` >> simp[SIGMA_ALGEBRA_SPACE,BIJ_IMAGE])
    >- (rename [`s ∈ _`] >> qexists_tac `space A DIFF s` >> simp[SIGMA_ALGEBRA_COMPL,EXTENSION] >>
        rw[] >> eq_tac >> strip_tac >> gvs[]
        >- (dxrule_then assume_tac BIJ_IMAGE >> gvs[] >> rename [`x ∈ _`] >> qexists_tac `x` >> simp[]) >>
        rename [`x ∈ _`] >> fs[BIJ_ALT,FUNSET,EXISTS_UNIQUE_ALT] >>
        NTAC 2 $ first_x_assum $ drule_then assume_tac >> fs[] >> qx_gen_tac `y` >>
        pop_assum (fn th => map_every (fn tm => qspec_then tm assume_tac th) [`x`,`y`]) >> gvs[] >>
        strip_tac >> fs[] >> Cases_on `y ∈ space A` >> fs[] >> pop_assum mp_tac >> simp[Once MONO_NOT_EQ] >>
        strip_tac >> dxrule_all_then mp_tac SIGMA_ALGEBRA_SUBSET_SPACE >> simp[SUBSET_DEF])
    >- (rename [`IMAGE tn`] >>
        `∃sn. tn = IMAGE f ∘ sn ∧ sn ∈ (𝕌(:num) → subsets A)` by (fs[FUNSET] >>
            simp[Once FUN_EQ_THM,FUNSET,GSYM FORALL_AND_THM,GSYM SKOLEM_THM]) >>
        gvs[] >> qpat_x_assum `_ ∘ _ ∈ _` kall_tac >> qexists_tac `BIGUNION (IMAGE sn 𝕌(:num))` >>
        simp[IMAGE_BIGUNION,IMAGE_COMPOSE,SIGMA_ALGEBRA_ENUM])
QED

Theorem PROD_SIGMA_Y_SLICE:
    ∀a b s x. subset_class (space a) (subsets a) ∧ sigma_algebra b ∧
        s ∈ subsets (a × b) ⇒ {y | (x,y) ∈ s} ∈ subsets b
Proof
    rw[] >> `sigma_algebra (a × b)` by (irule SIGMA_ALGEBRA_PROD_SIGMA >> simp[SIGMA_ALGEBRA_SUBSET_CLASS]) >>
    REVERSE $ Cases_on `x ∈ space a`
    >- (dxrule_all_then mp_tac SIGMA_ALGEBRA_SUBSET_SPACE >> simp[SUBSET_DEF,SPACE_PROD_SIGMA] >> strip_tac >>
        `{y | (x,y) ∈ s} = ∅` suffices_by simp[SIGMA_ALGEBRA_EMPTY] >> simp[EXTENSION] >> qx_gen_tac `y` >>
        CCONTR_TAC >> fs[] >> first_x_assum $ dxrule_then mp_tac >> simp[]) >>
    fs[SUBSETS_PROD_SIGMA] >>
    first_x_assum $ qspec_then `subsets (a × b) ∩ {t | {y | (x,y) ∈ t} ∈ subsets b}` $
        irule o cj 2 o SIMP_RULE (srw_ss ()) [] >>
    simp[SIGMA_ALGEBRA_ALT_SPACE] >> rpt CONJ_TAC
    >- (dxrule_then mp_tac SIGMA_ALGEBRA_SUBSET_CLASS >> simp[subset_class_def,SPACE_PROD_SIGMA])
    >- (dxrule_then mp_tac SIGMA_ALGEBRA_SPACE >> simp[SPACE_PROD_SIGMA])
    >- (simp[SIGMA_ALGEBRA_SPACE])
    >- (NTAC 2 strip_tac >> NTAC 2 $ dxrule_all_then mp_tac SIGMA_ALGEBRA_COMPL >>
        simp[SPACE_PROD_SIGMA,DIFF_DEF])
    >- (simp[FUNSET_INTER] >> NTAC 2 strip_tac >> simp[SIGMA_ALGEBRA_ENUM] >>
        qspecl_then [`b`,`λn. {y | (x,y) ∈ f n}`] mp_tac SIGMA_ALGEBRA_ENUM >> fs[FUNSET] >>
        qmatch_abbrev_tac `s ∈ _ ⇒ t ∈ _` >> `s = t` suffices_by simp[] >> UNABBREV_ALL_TAC >>
        simp[EXTENSION,IN_BIGUNION_IMAGE] >> qx_gen_tac `y` >> metis_tac[])
    >- (simp[prod_sets_def,SUBSET_DEF] >> rw[] >> rename [`s × t`] >> Cases_on `x ∈ s`
        >- (`{y | (x,y) ∈ s × t} = t` suffices_by simp[] >> simp[EXTENSION])
        >- (`{y | (x,y) ∈ s × t} = ∅` suffices_by simp[SIGMA_ALGEBRA_EMPTY] >> simp[EXTENSION]))
    >- (simp[prod_sigma_def,SIGMA_SUBSET_SUBSETS])
QED

Theorem PROD_SIGMA_STABLE_RIGHT:
    ∀a b. subset_class (space a) (subsets a) ∧ subset_class (space b) (subsets b) ∧
        space a ∈ subsets a ∧ space b ∈ subsets b ⇒
        a × sigma (space b) (subsets b) = a × b
Proof
    rw[prod_sigma_def,SPACE_SIGMA] >> irule SIGMA_CONG >> irule SUBSET_ANTISYM >> REVERSE CONJ_TAC
    >- (irule SIGMA_MONOTONE >> irule SUBSET_PROD_SETS >> simp[SIGMA_SUBSET_SUBSETS]) >> irule SIGMA_BOUNDED >>
    REVERSE $ Cases_on `subset_class (space a × space b) (prod_sets (subsets a) (subsets b))`
    >- (simp[SIGMA_EXPLODE]) >> rpt $ dxrule_then assume_tac SIGMA_ALGEBRA_SIGMA >>
    rw[Once SUBSET_DEF] >> rename [`sa × sb`] >>
    `sa × sb = (sa × (space b)) ∩ ((space a) × sb)` by (simp[SET_EQ_SUBSET,GSYM CONJ_ASSOC] >>
        NTAC 2 $ irule_at Any SUBSET_CROSS >> simp[] >>
        `sa ∈ subsets (sigma (space a) (subsets a))` by simp[IN_SIGMA] >>
        NTAC 2 $ dxrule_all_then mp_tac SIGMA_ALGEBRA_SUBSET_SPACE >> simp[SPACE_SIGMA] >>
        rw[] >> rw[SUBSET_DEF]) >>
    pop_assum SUBST1_TAC >> irule SIGMA_ALGEBRA_INTER >> simp[] >> CONJ_TAC
    >- (irule IN_SIGMA >> simp[prod_sets_def] >> qexistsl_tac [`sa`,`space b`] >> simp[]) >>
    qmatch_abbrev_tac `_ ∈ subsets sprs` >> Cases_on `space a = ∅` >> simp[SIGMA_ALGEBRA_EMPTY] >>
    qspecl_then [`space b`,`subsets b`,`λsb. space a × sb ∈ subsets sprs`,`sb`]
        (irule o SIMP_RULE (srw_ss ()) []) SIGMA_PROPERTY_WEAK_ALT >>
    `space a × space b ∈ subsets sprs ∧ subset_class (space a × space b) (subsets sprs)` by (
        fs[Abbr `sprs`,SIGMA_ALGEBRA_ALT_SPACE,SPACE_SIGMA]) >>
    qexists_tac `b` >> simp[] >> simp[SIGMA_ALGEBRA_ALT_SPACE] >> rw[]
    >- (fs[subset_class_def] >> qx_gen_tac `t` >> strip_tac >> first_x_assum $ dxrule_then mp_tac >>
        simp[SUBSET_DEF,FORALL_PROD] >> rw[] >> first_x_assum irule >> simp[] >> fs[MEMBER_NOT_EMPTY])
    >- (`space a × (space b DIFF s) = (space a × space b) DIFF (space a × s)` suffices_by (
            simp[SIGMA_ALGEBRA_DIFF]) >>
        simp[EXTENSION,FORALL_PROD] >> rw[] >> eq_tac >> rw[])
    >- (simp[CROSS_BIGUNION] >> irule SIGMA_ALGEBRA_ENUM >> fs[FUNSET])
    >- (simp[SUBSET_DEF,Abbr `sprs`] >> qx_gen_tac `t` >> strip_tac >>
        irule IN_SIGMA >> simp[prod_sets_def] >> qexistsl_tac [`space a`,`t`] >> simp[])
QED

Theorem PROD_SIGMA_STABLE:
    ∀a b. subset_class (space a) (subsets a) ∧ subset_class (space b) (subsets b) ∧
        space a ∈ subsets a ∧ space b ∈ subsets b ⇒
        (sigma (space a) (subsets a) × sigma (space b) (subsets b)) = a × b
Proof
    rw[prod_sigma_def,SPACE_SIGMA] >> irule SIGMA_CONG >> irule SUBSET_ANTISYM >> REVERSE CONJ_TAC
    >- (irule SIGMA_MONOTONE >> irule SUBSET_PROD_SETS >> simp[SIGMA_SUBSET_SUBSETS]) >> irule SIGMA_BOUNDED >>
    REVERSE $ Cases_on `subset_class (space a × space b) (prod_sets (subsets a) (subsets b))`
    >- (simp[SIGMA_EXPLODE]) >> rpt $ dxrule_then assume_tac SIGMA_ALGEBRA_SIGMA >>
    rw[Once SUBSET_DEF] >> rename [`sa × sb`] >>
    `sa × sb = (sa × (space b)) ∩ ((space a) × sb)` by (simp[SET_EQ_SUBSET,GSYM CONJ_ASSOC] >>
        NTAC 2 $ irule_at Any SUBSET_CROSS >> simp[] >>
        NTAC 2 $ dxrule_all_then mp_tac SIGMA_ALGEBRA_SUBSET_SPACE >> simp[SPACE_SIGMA] >>
        rw[] >> rw[SUBSET_DEF]) >>
    pop_assum SUBST1_TAC >> irule SIGMA_ALGEBRA_INTER >> simp[] >>
    qmatch_abbrev_tac `_ ∈ subsets sprs ∧ _` >>
    `(space b ≠ ∅ ⇒ sa × space b ∈ subsets sprs) ∧ (space a ≠ ∅ ⇒ space a × sb ∈ subsets sprs)` suffices_by (
        Cases_on `space a = ∅` >> Cases_on `space b = ∅` >> simp[SIGMA_ALGEBRA_EMPTY]) >>
    `space a × space b ∈ subsets sprs ∧ subset_class (space a × space b) (subsets sprs)` by (
        fs[Abbr `sprs`,SIGMA_ALGEBRA_ALT_SPACE,SPACE_SIGMA]) >>
    let fun tac tms = qspecl_then tms (irule o SIMP_RULE (srw_ss ()) []) SIGMA_PROPERTY_WEAK_ALT
    in rw[] >| [tac [`space a`,`subsets a`,`λsa. sa × space b ∈ subsets sprs`,`sa`],
        tac [`space b`,`subsets b`,`λsb. space a × sb ∈ subsets sprs`,`sb`]] end
    >| [qexists_tac `a`,qexists_tac `b`] >> simp[] >> simp[SIGMA_ALGEBRA_ALT_SPACE] >> rw[]
    >- (fs[subset_class_def] >> qx_gen_tac `s` >> strip_tac >> first_x_assum $ dxrule_then mp_tac >>
        simp[SUBSET_DEF,FORALL_PROD] >> rw[] >> first_x_assum irule >> simp[] >> fs[MEMBER_NOT_EMPTY])
    >- (`(space a DIFF s) × space b = (space a × space b) DIFF (s × space b)` suffices_by (
            simp[SIGMA_ALGEBRA_DIFF]) >>
        simp[EXTENSION,FORALL_PROD] >> rw[] >> eq_tac >> rw[])
    >- (simp[BIGUNION_CROSS] >> irule SIGMA_ALGEBRA_ENUM >> fs[FUNSET])
    >- (simp[SUBSET_DEF,Abbr `sprs`] >> qx_gen_tac `s` >> strip_tac >>
        irule IN_SIGMA >> simp[prod_sets_def] >> qexistsl_tac [`s`,`space b`] >> simp[])
    >- (fs[subset_class_def] >> qx_gen_tac `t` >> strip_tac >> first_x_assum $ dxrule_then mp_tac >>
        simp[SUBSET_DEF,FORALL_PROD] >> rw[] >> first_x_assum irule >> simp[] >> fs[MEMBER_NOT_EMPTY])
    >- (`space a × (space b DIFF s) = (space a × space b) DIFF (space a × s)` suffices_by (
            simp[SIGMA_ALGEBRA_DIFF]) >>
        simp[EXTENSION,FORALL_PROD] >> rw[] >> eq_tac >> rw[])
    >- (simp[CROSS_BIGUNION] >> irule SIGMA_ALGEBRA_ENUM >> fs[FUNSET])
    >- (simp[SUBSET_DEF,Abbr `sprs`] >> qx_gen_tac `t` >> strip_tac >>
        irule IN_SIGMA >> simp[prod_sets_def] >> qexistsl_tac [`space a`,`t`] >> simp[])
QED

Theorem SIGMA_PROD_ITR:
    ∀a b c. subset_class (space a) (subsets a) ∧ subset_class (space b) (subsets b) ∧
        subset_class (space c) (subsets c) ∧ space a ∈ subsets a ∧ space b ∈ subsets b ∧ space c ∈ subsets c ⇒
        subset_class (space b × space c) (prod_sets (subsets b) (subsets c)) ∧
        (space b × space c) ∈ (prod_sets (subsets b) (subsets c)) ∧
        a × sigma (space b × space c) (prod_sets (subsets b) (subsets c)) =
        sigma (space a × space b × space c) (prod_sets (subsets a) (prod_sets (subsets b) (subsets c)))
Proof
    rpt gen_tac >> strip_tac >> CONJ_ASM1_TAC >- simp[SUBSET_CLASS_PROD_SETS] >> CONJ_ASM1_TAC
    >- (simp[] >> qexistsl_tac [`space b`,`space c`] >> simp[]) >>
    qspecl_then [`a`,`space b × space c,prod_sets (subsets b) (subsets c)`]
        (SUBST1_TAC o SYM o SIMP_RULE (srw_ss ()) []) prod_sigma_def >>
    qspecl_then [`a`,`space b × space c,prod_sets (subsets b) (subsets c)`]
        (irule o SIMP_RULE (srw_ss ()) [Excl "IN_PROD_SETS"]) PROD_SIGMA_STABLE_RIGHT >> simp[]
QED

Definition pi_system_def:
    pi_system p ⇔ subset_class (space p) (subsets p) ∧ (subsets p ≠ ∅) ∧
        ∀s t. s ∈ subsets p ∧ t ∈ subsets p ⇒ s ∩ t ∈ subsets p
End

Theorem SIGMA_PI_LAMBDA:
    ∀a. sigma_algebra a ⇔ pi_system a ∧ dynkin_system a
Proof
    rw[pi_system_def,dynkin_system_def,GSYM DYNKIN_LEMMA] >> eq_tac >> rw[] >>
    simp[GSYM MEMBER_NOT_EMPTY] >> qexists_tac `space a` >> simp[]
QED

Theorem DYNKIN_SYSTEM_DIFF:
    ∀d s t. dynkin_system d ∧ s ∈ subsets d ∧ t ∈ subsets d ∧ s ⊆ t ⇒ t DIFF s ∈ subsets d
Proof
    rw[DYNKIN_SYSTEM_ALT_MONO]
QED

Theorem PI_LAMBDA_THM:
    ∀sp p d. pi_system (sp,p) ∧ p ⊆ d ∧ dynkin_system (sp,d) ⇒ subsets (sigma sp p) ⊆ d
Proof
    rw[pi_system_def] >> dxrule_all_then SUBST1_TAC $ GSYM DYNKIN_THM >>
    dxrule_then (qspec_then `sp` mp_tac) DYNKIN_MONOTONE >> dxrule DYNKIN_STABLE >> simp[]
QED

(*---------------------------------------------------------------------------*)
(* Trivial stuff for Measurable Functions *)
(*---------------------------------------------------------------------------*)

Theorem IN_MEASURABLE_CONG:
    ∀a b f g. (∀x. x ∈ space a ⇒ g x = f x) ∧ f ∈ measurable a b ⇒ g ∈ measurable a b
Proof
    rw[measurable_def] >- fs[FUNSET] >> first_x_assum $ dxrule_then mp_tac >>
    `PREIMAGE g s ∩ space a = PREIMAGE f s ∩ space a` suffices_by simp[] >>
    rw[EXTENSION] >> Cases_on `x ∈ space a` >> fs[]
QED

Theorem IN_MEASURABLE_COMP:
    ∀f g h a b c. f ∈ measurable a b ∧ g ∈ measurable b c ∧ (∀x. x ∈ space a ⇒ h x = g (f x)) ⇒
        h ∈ measurable a c
Proof
    rw[] >> irule IN_MEASURABLE_CONG >> qexists_tac `g ∘ f` >> simp[MEASURABLE_COMP,SF SFY_ss]
QED

Theorem IN_MEASURABLE_FST:
    ∀a b. sigma_algebra a ∧ sigma_algebra b ⇒ FST ∈ measurable (a × b) a
Proof
    rw[] >> simp[IN_MEASURABLE,SIGMA_ALGEBRA_PROD_SIGMA_WEAK,FUNSET,IN_SPACE_PROD_SIGMA] >> rw[] >>
    `PREIMAGE FST s ∩ space (a × b) = s × (space b)` by (simp[EXTENSION,IN_SPACE_PROD_SIGMA] >>
        rw[] >> eq_tac >> rw[] >> dxrule_all_then mp_tac SIGMA_ALGEBRA_SUBSET_SPACE >> simp[SUBSET_DEF]) >>
    pop_assum SUBST1_TAC >> simp[prod_sigma_def] >> irule IN_SIGMA >>
    simp[prod_sets_def] >> qexistsl_tac [`s`,`space b`] >> simp[SIGMA_ALGEBRA_SPACE]
QED

Theorem IN_MEASURABLE_SND:
    ∀a b. sigma_algebra a ∧ sigma_algebra b ⇒ SND ∈ measurable (a × b) b
Proof
    rw[] >> simp[IN_MEASURABLE,SIGMA_ALGEBRA_PROD_SIGMA_WEAK,FUNSET,IN_SPACE_PROD_SIGMA] >> rw[] >>
    `PREIMAGE SND s ∩ space (a × b) = (space a) × s` by (simp[EXTENSION,IN_SPACE_PROD_SIGMA] >>
        rw[] >> eq_tac >> rw[] >> dxrule_all_then mp_tac SIGMA_ALGEBRA_SUBSET_SPACE >> simp[SUBSET_DEF]) >>
    pop_assum SUBST1_TAC >> simp[prod_sigma_def] >> irule IN_SIGMA >>
    simp[prod_sets_def] >> qexistsl_tac [`space a`,`s`] >> simp[SIGMA_ALGEBRA_SPACE]
QED

Theorem IN_MEASURABLE_PROD_SIGMA:
    ∀a bx by fx fy f. sigma_algebra a ∧ fx ∈ measurable a bx ∧ fy ∈ measurable a by ∧
        (∀z. z ∈ space a ⇒ f z = (fx z,fy z)) ⇒ f ∈ measurable a (bx × by)
Proof
    rw[] >> irule IN_MEASURABLE_CONG >> qexists_tac `λz. (fx z,fy z)` >> simp[] >>
    irule MEASURABLE_PROD_SIGMA' >> simp[o_DEF,ETA_AX]
QED

Theorem IN_MEASURABLE_ALT:
    ∀f a b. f ∈ measurable a b ⇔ ∃ar br.
        sigma (space a) ar = a ∧ sigma (space b) br = b ∧ subset_class (space a) ar ∧
        subset_class (space b) br ∧ f ∈ (space a → space b) ∧
        ∀s. s ∈ br ⇒ PREIMAGE f s ∩ space a ∈ ar
Proof
    rw[IN_MEASURABLE] >> eq_tac >> strip_tac
    >- (qexistsl_tac [`subsets a`,`subsets b`] >> simp[SIGMA_STABLE,SIGMA_ALGEBRA_SUBSET_CLASS]) >>
    map_every qabbrev_tac [`asp = space a`,`bsp = space b`] >> NTAC 2 $ pop_assum kall_tac >>
    NTAC 2 $ last_x_assum $ SUBST1_TAC o SYM >> NTAC 2 $ irule_at Any SIGMA_ALGEBRA_SIGMA >> simp[] >>
    `sigma_algebra (bsp,{s | s ⊆ bsp ∧ PREIMAGE f s ∩ asp ∈ subsets (sigma asp ar)})` suffices_by (
        rw[sigma_def] >> first_x_assum (fn th => first_x_assum $ C (resolve_then Any assume_tac) th) >>
        fs[] >> pop_assum $ irule o cj 2 >> simp[] >> simp[SUBSET_DEF] >> fs[subset_class_def,SUBSET_DEF]) >>
    simp[SIGMA_ALGEBRA_ALT_SPACE,subset_class_def,FUNSET] >>
    NTAC 2 $ dxrule_then assume_tac SIGMA_ALGEBRA_SIGMA >> rpt CONJ_TAC
    >- (`PREIMAGE f bsp ∩ asp = asp` by (simp[EXTENSION] >> rw[] >> eq_tac >> rw[] >> fs[FUNSET]) >>
        pop_assum SUBST1_TAC >> NTAC 2 $ dxrule_then assume_tac SIGMA_ALGEBRA_SPACE >> fs[SPACE_SIGMA])
    >- (rw[] >> dxrule_all_then mp_tac SIGMA_ALGEBRA_COMPL >> simp[SPACE_SIGMA] >>
        `PREIMAGE f (bsp DIFF s) ∩ asp = asp DIFF PREIMAGE f s ∩ asp` suffices_by simp[] >>
        rw[EXTENSION] >> eq_tac  >> rw[] >> fs[FUNSET])
    >- (qx_gen_tac `sn` >> rw[] >- (simp[SUBSET_DEF,IN_BIGUNION_IMAGE] >> rw[] >> fs[SUBSET_DEF,SF SFY_ss]) >>
        simp[PREIMAGE_BIGUNION,GSYM BIGUNION_IMAGE_INTER_RIGHT,IMAGE_IMAGE] >>
        irule SIGMA_ALGEBRA_COUNTABLE_UNION >> simp[] >> rw[SUBSET_DEF] >> simp[])
QED

Theorem IN_MEASURABLE_BOREL_FROM_PROD_SIGMA_ALT:
    ∀a b f. sigma_algebra a ∧ sigma_algebra b ∧ f ∈ Borel_measurable (a × b) ⇒
        (∀y. y ∈ space b ⇒ (λx. f (x,y)) ∈ Borel_measurable a) ∧
        (∀x. x ∈ space a ⇒ (λy. f (x,y)) ∈ Borel_measurable b)
Proof
    rpt gen_tac >> DISCH_TAC >>
    qspecl_then [`space a`,`space b`,`subsets a`,`subsets b`,`f`] mp_tac IN_MEASURABLE_BOREL_FROM_PROD_SIGMA >>
    simp[]
QED

Theorem IN_MEASURABLE_BOREL_CONG:
    ∀sa f g. (∀x. x ∈ space sa ⇒ g x = f x) ∧ f ∈ Borel_measurable sa ⇒
       g ∈ Borel_measurable sa
Proof
    rw[] >> qspecl_then [`(space sa,subsets sa,_)`,`g`,`f`] assume_tac $ IN_MEASURABLE_BOREL_EQ >> fs[]
QED

Theorem IN_MEASURABLE_BOREL_SUM':
    ∀a f g s. FINITE s ∧ sigma_algebra a ∧ (∀i. i ∈ s ⇒ f i ∈ Borel_measurable a) ∧
        (∀x. x ∈ space a ⇒ g x = ∑ (λi. f i x) s) ⇒ g ∈ Borel_measurable a
Proof
    `∀a f g l. sigma_algebra a ∧ (∀i. MEM i l ⇒ f i ∈ Borel_measurable a) ∧
      (∀x. x ∈ space a ⇒ g x = FOLDR (λi acc. f i x + acc) 0 l) ⇒ g ∈ Borel_measurable a` suffices_by (
        rw[] >> last_x_assum irule >> simp[] >> qexistsl_tac [`f`,`REV_CHOICE_LIST s`] >>
        simp[EXTREAL_SUM_IMAGE_ALT_FOLDR,SF SFY_ss] >> rw[] >> first_x_assum irule >>
        pop_assum mp_tac >> simp[REV_CHOICE_LIST_ALT]) >>
    Induct_on `l` >> rw[FOLDR]
    >- (irule IN_MEASURABLE_BOREL_CONST >> simp[] >> qexists_tac `0` >> simp[]) >>
    irule IN_MEASURABLE_BOREL_ADD' >> simp[] >>
    qexistsl_tac [`f h`,`λx. FOLDR (λi acc. f i x + acc) 0 l`] >> simp[] >>
    last_x_assum irule >> simp[] >> qexists_tac `f` >> simp[]
QED

Theorem IN_MEASURABLE_BOREL_MUL' = IN_MEASURABLE_BOREL_TIMES';

(* could do a prime of this *)
Theorem IN_MEASURABLE_BOREL_PROD:
    ∀a f g s. FINITE s ∧ sigma_algebra a ∧ (∀i. i ∈ s ⇒ f i ∈ Borel_measurable a) ∧
        (∀i x. i ∈ s ∧ x ∈ space a ⇒ f i x ≠ −∞ ∧ f i x ≠ +∞) ∧
        (∀x. x ∈ space a ⇒ g x = ∏ (λi. f i x) s) ⇒
        g ∈ Borel_measurable a
Proof
    NTAC 2 gen_tac >> simp[Once SWAP_FORALL_THM,Once $ GSYM AND_IMP_INTRO,RIGHT_FORALL_IMP_THM] >>
    Induct_on `s` >> rw[]
    >- (fs[EXTREAL_PROD_IMAGE_EMPTY] >> irule IN_MEASURABLE_BOREL_CONST >>
        simp[] >> qexists_tac `1` >> simp[]) >>
    rfs[EXTREAL_PROD_IMAGE_PROPERTY,DELETE_NON_ELEMENT_RWT] >>
    irule IN_MEASURABLE_BOREL_MUL >> simp[] >> qexistsl_tac [`f e`,`λx. ∏ (λi. f i x) s`] >>
    simp[] >> NTAC 2 strip_tac >> irule EXTREAL_PROD_IMAGE_NOT_INFTY >> simp[]
QED

Theorem IN_MEASURABLE_BOREL_COMP:
    ∀a b f g h. sigma_algebra a ∧ sigma_algebra b ∧ f ∈ Borel_measurable b ∧ g ∈ measurable a b ∧
        (∀x. x ∈ space a ⇒ h x = f (g x)) ⇒ h ∈ Borel_measurable a
Proof
    rw[] >> dxrule_all_then assume_tac MEASURABLE_COMP >>
    irule IN_MEASURABLE_BOREL_EQ' >> qexists_tac `f ∘ g` >> simp[]
QED

Theorem IN_MEASURABLE_BOREL_COMP_BOREL:
    ∀a f g h. sigma_algebra a ∧ f ∈ Borel_measurable Borel ∧ g ∈ Borel_measurable a ∧
        (∀x. x ∈ space a ⇒ h x = f (g x)) ⇒ h ∈ Borel_measurable a
Proof
    rw[] >> dxrule_all_then assume_tac MEASURABLE_COMP >>
    irule IN_MEASURABLE_BOREL_EQ' >> qexists_tac `f ∘ g` >> simp[]
QED

Theorem IN_MEASURABLE_BOREL_INV:
    ∀a f g. sigma_algebra a ∧ f ∈ Borel_measurable a ∧
        (∀x. x ∈ space a ⇒ g x = (f x)⁻¹ * 𝟙 {y | f y ≠ 0} x) ⇒
        g ∈ Borel_measurable a
Proof
    rw[] >> simp[IN_MEASURABLE_BOREL,FUNSET] >>
    `(∀c. c ≤ 0 ⇒ {x | g x < Normal c} ∩ space a ∈ subsets a) ∧
      {x | g x = 0} ∩ space a ∈ subsets a ∧
      (∀c. 0 < c ⇒ {x | 0 < g x ∧ g x < Normal c} ∩ space a ∈ subsets a)` suffices_by (
        rw[] >> Cases_on `c ≤ 0` >> simp[] >> fs[REAL_NOT_LE] >>
        first_x_assum $ drule_then assume_tac >> first_x_assum $ qspec_then `0` assume_tac >>
        fs[normal_0] >> drule_then (fn th => NTAC 2 $ dxrule_all_then assume_tac th) SIGMA_ALGEBRA_UNION >>
        pop_assum mp_tac >> qmatch_abbrev_tac `s ∈ _ ⇒ t ∈ _` >> `s = t` suffices_by simp[] >>
        UNABBREV_ALL_TAC >> rw[EXTENSION] >> qpat_x_assum `∀x. _` kall_tac >>
        Cases_on `x ∈ space a` >> simp[] >> Cases_on `g x` >> simp[]) >>
    rw[]
    >- (drule_then (qspecl_then [`if c = 0 then −∞ else Normal c⁻¹`,`0`] mp_tac) IN_MEASURABLE_BOREL_OO >>
        qmatch_abbrev_tac `s ∈ _ ⇒ t ∈ _` >> `s = t` suffices_by simp[] >> UNABBREV_ALL_TAC >>
        simp[EXTENSION] >> strip_tac >> Cases_on `x ∈ space a` >> simp[indicator_fn_def] >>
        Cases_on `f x` >> rw[extreal_inv_def] >> eq_tac >> strip_tac >> simp[] >>
        drule_all_then assume_tac REAL_LTE_TRANS >> fs[])
    >- (drule_all_then assume_tac IN_MEASURABLE_BOREL_SING >>
        pop_assum (fn th => map_every (fn tm => qspec_then tm assume_tac th) [`−∞`,`0`,`+∞`]) >>
        drule_then (fn th => NTAC 2 $ dxrule_all_then assume_tac th) SIGMA_ALGEBRA_UNION >>
        pop_assum mp_tac >> qmatch_abbrev_tac `s ∈ _ ⇒ t ∈ _` >> `s = t` suffices_by simp[] >>
        UNABBREV_ALL_TAC >> rw[EXTENSION] >> Cases_on `x ∈ space a` >> simp[indicator_fn_def] >>
        Cases_on `f x` >> rw[extreal_inv_def])
    >- (drule_then (qspecl_then [`Normal c⁻¹`,`+∞`] mp_tac) IN_MEASURABLE_BOREL_OO >>
        qmatch_abbrev_tac `s ∈ _ ⇒ t ∈ _` >> `s = t` suffices_by simp[] >> UNABBREV_ALL_TAC >>
        rw[EXTENSION] >> Cases_on `x ∈ space a` >> simp[indicator_fn_def] >>
        Cases_on `f x` >> rw[extreal_inv_def] >> simp[] >> eq_tac >> strip_tac >> rfs[] >>
        REVERSE CONJ_ASM1_TAC >- simp[] >> `0 ≤ c * r` by simp[] >> rfs[REAL_MUL_SIGN])
QED

Theorem IN_MEASURABLE_BOREL_MUL_INV:
    ∀a f g h. sigma_algebra a ∧ f ∈ Borel_measurable a ∧ g ∈ Borel_measurable a ∧
        (∀x. x ∈ space a ∧ g x = 0 ⇒ f x = 0) ∧ (∀x. x ∈ space a ⇒ h x = f x * (g x)⁻¹) ⇒
        h ∈ Borel_measurable a
Proof
    rw[] >> irule IN_MEASURABLE_BOREL_MUL' >> simp[] >>
    qexistsl_tac [`f`,`λx. (g x)⁻¹ * 𝟙 {y | g y ≠ 0} x`] >> simp[] >>
    irule_at Any IN_MEASURABLE_BOREL_INV >>
    qexists_tac `g` >> simp[] >> rw[indicator_fn_def] >> simp[]
QED

Theorem IN_MEASURABLE_BOREL_EXP:
    ∀a f g. sigma_algebra a ∧ f ∈ Borel_measurable a ∧ (∀x. x ∈ space a ⇒ g x = exp (f x)) ⇒
        g ∈ Borel_measurable a
Proof
    rw[] >> irule IN_MEASURABLE_BOREL_COMP_BOREL >> simp[] >> qexistsl_tac [`exp`,`f`] >> simp[] >>
    rw[IN_MEASURABLE_BOREL_ALT2,SIGMA_ALGEBRA_BOREL,FUNSET,SPACE_BOREL] >> Cases_on `c < 0`
    >- (`{x | exp x ≤ Normal c} = ∅` suffices_by simp[BOREL_MEASURABLE_SETS_EMPTY] >>
        rw[EXTENSION,GSYM extreal_lt_def] >> irule lte_trans >> qexists_tac `0` >> simp[exp_pos]) >>
    `{x | exp x ≤ Normal c} = {x | x ≤ ln (Normal c)}` suffices_by simp[BOREL_MEASURABLE_SETS_RC] >>
    fs[GSYM real_lte] >> rw[EXTENSION] >> REVERSE (fs[REAL_LE_LT])
    >- (simp[extreal_ln_def,normal_0] >> Cases_on `x` >>
        simp[extreal_exp_def,GSYM real_lt,EXP_POS_LT]) >>
    drule_then SUBST1_TAC $ GSYM $ iffRL EXP_LN >> simp[Once $ GSYM extreal_exp_def,exp_mono_le] >>
    simp[iffRL EXP_LN,extreal_ln_def]
QED

Theorem IN_MEASURABLE_BOREL_POW':
    ∀n a f g. sigma_algebra a ∧ f ∈ Borel_measurable a ∧ (∀x. x ∈ space a ⇒ g x = f x pow n) ⇒
        g ∈ Borel_measurable a
Proof
    Induct_on `n` >> rw[extreal_pow_alt]
    >- (irule IN_MEASURABLE_BOREL_CONST >> simp[] >> qexists_tac `1` >> simp[])
    >- (irule IN_MEASURABLE_BOREL_MUL' >> simp[] >> qexistsl_tac [`(λx. f x pow n)`,`f`] >> simp[] >>
        last_x_assum irule >> simp[] >> qexists_tac `f` >> simp[])
QED

Theorem IN_MEASURABLE_BOREL_POW_EXP:
    ∀a f g h. sigma_algebra a ∧ f ∈ Borel_measurable a ∧
        (∀n. {x | g x = n} ∩ space a ∈ subsets a) ∧
        (∀x. x ∈ space a ⇒ h x = (f x) pow (g x)) ⇒ h ∈ Borel_measurable a
Proof
    rw[] >> simp[Once IN_MEASURABLE_BOREL_PLUS_MINUS] >>
    `∀P. {x | P (g x)} ∩ space a ∈ subsets a` by (rw[] >>
        `{x | P (g x)} ∩ space a = BIGUNION {{x | g x = n} ∩ space a | P n}` by (
            rw[Once EXTENSION,IN_BIGUNION] >> eq_tac >> strip_tac >> gvs[] >>
            qexists_tac `{y | g y = g x} ∩ space a` >> simp[] >> qexists_tac `g x` >> simp[]) >>
        pop_assum SUBST1_TAC >> irule SIGMA_ALGEBRA_COUNTABLE_UNION >>
        REVERSE (rw[SUBSET_DEF]) >- simp[SF SFY_ss] >> simp[COUNTABLE_ALT] >>
        qexists_tac `λn. {x | g x = n} ∩ space a` >> rw[] >> qexists_tac `n` >> simp[]) >>
    map_every (fn (pos,tm,qex,ths) => irule_at pos tm >> qexistsl_tac qex >> simp ths) [
        (Pos hd,IN_MEASURABLE_BOREL_ADD',[`λx. f⁻ x pow g x * 𝟙 {x | EVEN (g x)} x`,
            `λx. f⁺ x pow g x * 𝟙 {x | $< 0 (g x)} x`],[]),
        (Pos (el 2),IN_MEASURABLE_BOREL_MUL',[`𝟙 {x | EVEN (g x)}`,`λx. f⁻ x pow g x`],[]),
        (Pos (el 2),IN_MEASURABLE_BOREL_INDICATOR,[`{x | EVEN (g x)} ∩ space a`],[]),
        (Pos (el 3),IN_MEASURABLE_BOREL_MUL',[`𝟙 {x | $< 0 (g x)}`,`λx. f⁺ x pow g x`],[]),
        (Pos (el 2),IN_MEASURABLE_BOREL_INDICATOR,[`{x | $< 0 (g x)} ∩ space a`],[]),
        (Pos last,IN_MEASURABLE_BOREL_MUL',[`𝟙 {x | ODD (g x)}`,`λx. f⁻ x pow g x`],[]),
        (Pos (el 2),IN_MEASURABLE_BOREL_INDICATOR,[`{x | ODD (g x)} ∩ space a`],[])] >>
    pop_assum kall_tac >>
    `∀pf. pf ∈ Borel_measurable a ∧ (∀x. 0 ≤ pf x) ⇒ (λx. pf x pow g x) ∈ Borel_measurable a` by (
        rw[] >> irule IN_MEASURABLE_BOREL_SUMINF >> simp[] >>
        qexistsl_tac [`λn x. pf x pow n * 𝟙 {x | g x = n} x`] >> simp[pow_pos_le,INDICATOR_FN_POS,le_mul] >>
        simp[RIGHT_AND_FORALL_THM] >> strip_tac >>
        map_every (fn (pos,tm,qex,ths) => irule_at pos tm >> simp[] >> qexistsl_tac qex >> simp ths) [
            (Any,IN_MEASURABLE_BOREL_MUL',[`𝟙 {x | g x = n}`,`λx. pf x pow n`],[]),
            (Pos hd,IN_MEASURABLE_BOREL_POW',[`n`,`pf`],[]),
            (Pos hd,IN_MEASURABLE_BOREL_INDICATOR,[`{x | g x = n} ∩ space a`],[indicator_fn_def])] >>
        rw[] >> qspecl_then [`g x`,`pf x pow g x`] mp_tac ext_suminf_sing_general >>
        simp[pow_pos_le] >> DISCH_THEN $ SUBST1_TAC o SYM >> irule IRULER >> rw[FUN_EQ_THM] >>
        Cases_on `g x = n` >> simp[]) >>
    pop_assum (fn th => NTAC 2 (irule_at Any th >> simp[iffLR IN_MEASURABLE_BOREL_PLUS_MINUS])) >>
    simp[FN_PLUS_POS,FN_MINUS_POS] >> rw[indicator_fn_def] >> simp[fn_minus_def,fn_plus_alt]
    >- (Cases_on `f x < 0` >- fs[pow_neg_odd,pow_ainv_odd] >> fs[ODD_POS,zero_pow] >>
        `¬(f x pow g x < 0)` suffices_by simp[] >> fs[extreal_lt_def,pow_pos_le])
    >- (`¬(f x pow g x < 0)` suffices_by simp[] >> fs[ODD_EVEN] >> simp[extreal_lt_def,pow_even_le])
    >- (Cases_on `0 ≤ f x` >> fs[GSYM extreal_lt_def] >>
        simp[ineq_imp,pow_pos_le,zero_pow,pow_even_le,pow_ainv_even])
    >- (fs[EVEN_ODD] >> Cases_on `0 ≤ f x` >> fs[GSYM extreal_lt_def] >> simp[ineq_imp,pow_pos_le,zero_pow] >>
        `¬(0 ≤ f x pow g x)` suffices_by simp[] >> simp[GSYM extreal_lt_def,pow_neg_odd])
    >- (Cases_on `0 ≤ f x` >> fs[GSYM extreal_lt_def] >> simp[ineq_imp])
    >- (rfs[EVEN_ODD,ODD])
QED

Definition bounded_Borel_measurable_def:
    bounded_Borel_measurable sa ⇔ {f | f ∈ Borel_measurable sa ∧
        ∃a b. f ∈ (space sa → closed_interval (Normal a) (Normal b))}
End

Theorem IN_BOUNDED_BOREL_MEASURABLE:
    ∀f sa. f ∈ bounded_Borel_measurable sa ⇔ f ∈ Borel_measurable sa ∧
        ∃a b. f ∈ (space sa → closed_interval (Normal a) (Normal b))
Proof
    simp[bounded_Borel_measurable_def]
QED

Theorem IN_BOUNDED_BOREL_MEASURABLE_CONG:
    ∀sa f g. (∀x. x ∈ space sa ⇒ g x = f x) ∧ f ∈ bounded_Borel_measurable sa ⇒
       g ∈ bounded_Borel_measurable sa
Proof
    rw[IN_BOUNDED_BOREL_MEASURABLE]
    >- (irule IN_MEASURABLE_BOREL_CONG >> qexists_tac `f` >> simp[])
    >- (qexistsl_tac [`a`,`b`] >> fs[FUNSET,closed_interval_def])
QED

Theorem IN_BOUNDED_BOREL_MEASURABLE_REAL_VALUED:
    ∀f sa. f ∈ bounded_Borel_measurable sa ⇒
        ∃rf. ∀x. x ∈ space sa ⇒ f x = Normal (rf x)
Proof
    rw[] >> qexists_tac `real ∘ f` >> rw[] >>
    fs[IN_BOUNDED_BOREL_MEASURABLE,FUNSET,closed_interval_def] >>
    last_x_assum $ dxrule_then assume_tac >> fs[] >>
    Cases_on `f x` >> fs[real_normal]
QED

Theorem IN_BOUNDED_BOREL_MEASURABLE_CONST:
    ∀sa c f. sigma_algebra sa ∧ (∀x. x ∈ space sa ⇒ f x = Normal c) ⇒
        f ∈ bounded_Borel_measurable sa
Proof
    rw[IN_BOUNDED_BOREL_MEASURABLE]
    >- (irule IN_MEASURABLE_BOREL_CONST >> simp[] >> qexists_tac `Normal c` >> simp[])
    >- (qexistsl_tac [`c`,`c`] >> rw[FUNSET,closed_interval_def])
QED

Theorem IN_BOUNDED_BOREL_MEASURABLE_INDICATOR:
    ∀sa s f. sigma_algebra sa ∧ s ∈ subsets sa ∧ (∀x. x ∈ space sa ⇒ f x = 𝟙 s x) ⇒
        f ∈ bounded_Borel_measurable sa
Proof
    rw[IN_BOUNDED_BOREL_MEASURABLE]
    >- (irule IN_MEASURABLE_BOREL_INDICATOR >> simp[] >> qexists_tac `s` >> simp[]) >>
    qexistsl_tac [`0`,`1`] >> rw[FUNSET] >> simp[closed_interval_def,indicator_fn_def] >>
    rw[normal_0,normal_1,le_01]
QED

Theorem IN_BOUNDED_BOREL_MEASURABLE_ADD:
    ∀sa f g h. f ∈ bounded_Borel_measurable sa ∧ g ∈ bounded_Borel_measurable sa ∧
        (∀x. x ∈ space sa ⇒ h x = f x + g x) ⇒ h ∈ bounded_Borel_measurable sa
Proof
    rw[IN_BOUNDED_BOREL_MEASURABLE]
    >- (irule IN_MEASURABLE_BOREL_ADD' >> irule_at Any $ cj 1 $ iffLR IN_MEASURABLE_BOREL >>
        qexistsl_tac [`g`,`f`,`f`] >> simp[]) >>
    qexistsl_tac [`a + a'`,`b + b'`] >> rename [`closed_interval (Normal (a + c)) (Normal (b + d))`] >>
    fs[FUNSET,closed_interval_def] >> rw[GSYM extreal_add_def] >> irule le_add2 >> fs[]
QED

Theorem IN_BOUNDED_BOREL_MEASURABLE_CMUL:
    ∀sa f g c. f ∈ bounded_Borel_measurable sa ∧
        (∀x. x ∈ space sa ⇒ g x = Normal c * f x) ⇒
        g ∈ bounded_Borel_measurable sa
Proof
    rw[IN_BOUNDED_BOREL_MEASURABLE]
    >- (irule IN_MEASURABLE_BOREL_CMUL >> irule_at Any $ cj 1 $ iffLR IN_MEASURABLE_BOREL >>
        qexistsl_tac [`c`,`f`,`f`] >> simp[]) >>
    `0 ≤ Normal c ∨ Normal c ≤ 0` by simp[le_total]
    >- (qexistsl_tac [`c * a`,`c * b`] >> rw[GSYM extreal_mul_def] >>
        fs[FUNSET,closed_interval_def] >> rw[] >> irule le_lmul_imp >> fs[])
    >- (qexistsl_tac [`c * b`,`c * a`] >> rw[GSYM extreal_mul_def] >>
        fs[FUNSET,closed_interval_def] >> rw[] >> irule le_lmul_neg_imp >> fs[])
QED

Theorem IN_BOUNDED_BOREL_MEASURABLE_MUL:
    ∀sa f g h. f ∈ bounded_Borel_measurable sa ∧ g ∈ bounded_Borel_measurable sa ∧
        (∀x. x ∈ space sa ⇒ h x = f x * g x) ⇒ h ∈ bounded_Borel_measurable sa
Proof
    rw[IN_BOUNDED_BOREL_MEASURABLE]
    >- (irule IN_MEASURABLE_BOREL_MUL >> irule_at Any $ cj 1 $ iffLR IN_MEASURABLE_BOREL >>
        qexistsl_tac [`g`,`f`,`f`] >> simp[] >>
        rw[] >> CCONTR_TAC >> fs[FUNSET,closed_interval_def] >>
        NTAC 2 $ last_x_assum $ drule_then mp_tac >> simp[])
    >- (qexistsl_tac [`-max (abs a) (abs b) * max (abs a') (abs b')`,
            `max (abs a) (abs b) * max (abs a') (abs b')`] >>
        fs[FUNSET] >> rw[] >> fs[closed_interval_def] >>
        fs[GSYM extreal_mul_def,GSYM extreal_ainv_def,GSYM max_normal,GSYM extreal_abs_def] >>
        irule closed_interval_mul >> fs[])
QED

Theorem IN_MEASURABLE_BOREL_NORMAL_REAL:
    ∀sa f. f ∈ Borel_measurable sa ⇒
       Normal ∘ real ∘ f ∈ Borel_measurable sa
Proof
    rw[] >> irule IN_MEASURABLE_BOREL_IMP_BOREL' >> irule_at Any in_borel_measurable_from_Borel >>
    simp[] >> fs[IN_MEASURABLE]
QED

(*---------------------------------------------------------------------------*)
(* Trivial stuff for Measure Spaces *)
(*---------------------------------------------------------------------------*)

Definition sig_alg_def:
    sig_alg m = (m_space m,measurable_sets m)
End

Theorem re_sig_alg:
    ∀m. (m_space m,measurable_sets m) = sig_alg m
Proof
    rw[sig_alg_def]
QED

val _ = mk_local_simp "re_sig_alg";

Theorem sig_alg_tripple:
    ∀sp sts mu. sig_alg (sp,sts,mu) = (sp,sts)
Proof
    rw[sig_alg_def,Excl "re_sig_alg"]
QED

val _ = mk_local_simp "sig_alg_tripple";

Theorem space_sig_alg:
    ∀m. space (sig_alg m) = m_space m
Proof
    rw[sig_alg_def,Excl "re_sig_alg"]
QED

val _ = mk_local_simp "space_sig_alg";

Theorem subsets_sig_alg:
    ∀m. subsets (sig_alg m) = measurable_sets m
Proof
    rw[sig_alg_def,Excl "re_sig_alg"]
QED

val _ = mk_local_simp "subsets_sig_alg";

Theorem MEASURE_SPACE_SIGMA_ALGEBRA:
    (∀m. measure_space (m:α m_space) ⇒ sigma_algebra (sig_alg m)) ∧
    (∀sa mu. measure_space ((space sa,subsets sa,mu):α m_space) ⇒ sigma_algebra sa) ∧
    (∀sp sts mu. measure_space ((sp,sts,mu):α m_space) ⇒ sigma_algebra (sp,sts))
Proof
    rw[measure_space_def]
QED

val _ = mk_local_simp "MEASURE_SPACE_SIGMA_ALGEBRA";

Theorem MEASURE_SPACE_SIGMA_STABLE:
    ∀m. measure_space m ⇒ sigma (m_space m) (measurable_sets m) = sig_alg m
Proof
    rw[measure_space_def] >> dxrule_then mp_tac SIGMA_STABLE >> simp[]
QED

Theorem MEASURE_SPACE_SUBSET_CLASS:
    ∀m. measure_space m ⇒ subset_class (m_space m) (measurable_sets m)
Proof
    simp[measure_space_def,SIGMA_ALGEBRA_ALT_SPACE]
QED

Theorem MEASURE_POSITIVE:
    ∀m s. measure_space m ∧ s ∈ measurable_sets m ⇒ 0 ≤ measure m s
Proof
    rw[] >> irule $ cj 2 $ iffLR positive_def >> simp[iffLR measure_space_def]
QED

Theorem MEASURE_INCREASING:
    ∀m s t. measure_space m ∧ s ∈ measurable_sets m ∧ t ∈ measurable_sets m ∧ s ⊆ t ⇒
        measure m s ≤ measure m t
Proof
    rw[] >> irule $ iffLR increasing_def >> simp[MEASURE_SPACE_INCREASING]
QED

Theorem MEASURE_CONG:
    ∀m s t. measure_space m ∧ s ∈ measurable_sets m ∧ t ∈ measurable_sets m ∧
        (∀x. x ∈ m_space m ⇒ (x ∈ s ⇔ x ∈ t)) ⇒ measure m s = measure m t
Proof
    rw[] >> irule IRULER >> simp[EXTENSION] >> qx_gen_tac `x` >>
    Cases_on `x ∈ m_space m` >- (first_x_assum $ qspec_then `x` mp_tac >> simp[]) >>
    imp_res_tac MEASURE_SPACE_IN_MSPACE >> NTAC 2 $ pop_assum $ qspec_then `x` mp_tac >> simp[]
QED

Theorem measure_upper_bound:
    ∀m s. measure_space m ∧ s ∈ measurable_sets m ⇒ measure m s ≤ measure m (m_space m)
Proof
    rw[] >> irule INCREASING >>
    simp[MEASURE_SPACE_INCREASING,MEASURE_SPACE_MSPACE_MEASURABLE,MEASURABLE_SETS_SUBSET_SPACE]
QED

Theorem NULL_SET_INTERL:
    ∀m s t. measure_space m ∧ s ∈ null_set m ∧ t ∈ measurable_sets m ⇒ s ∩ t ∈ null_set m
Proof
    rw[] >> fs[IN_NULL_SET,null_set_def] >> CONJ_ASM1_TAC >- simp[MEASURE_SPACE_INTER] >>
    qspecl_then [`m`,`s ∩ t`,`s`] mp_tac MEASURE_INCREASING >> simp[GSYM le_antisym,MEASURE_POSITIVE]
QED

Theorem NULL_SET_INTERR:
    ∀m s t. measure_space m ∧ s ∈ measurable_sets m ∧ t ∈ null_set m ⇒ s ∩ t ∈ null_set m
Proof
    rw[] >> fs[IN_NULL_SET,null_set_def] >> CONJ_ASM1_TAC >- simp[MEASURE_SPACE_INTER] >>
    qspecl_then [`m`,`s ∩ t`,`t`] mp_tac MEASURE_INCREASING >> simp[GSYM le_antisym,MEASURE_POSITIVE]
QED

Theorem MEASURE_CONG_AE:
    ∀m s t. measure_space m ∧ s ∈ measurable_sets m ∧ t ∈ measurable_sets m ∧
        (AE x::m. x ∈ s ⇔ x ∈ t) ⇒ measure m s = measure m t
Proof
    rw[] >> fs[AE_ALT] >> rename [`null_set m r`] >> fs[SUBSET_DEF] >>
    map_every (fn tml => qspecl_then tml assume_tac NULL_SET_INTERR) [[`m`,`s`,`r`],[`m`,`t`,`r`]] >>
    map_every (fn tml => qspecl_then tml assume_tac MEASURE_DIFF_SUBSET)
        [[`m`,`s`,`s ∩ r`],[`m`,`t`,`t ∩ r`]] >>
    rfs[IN_NULL_SET,null_set_def] >> NTAC 2 $ pop_assum $ SUBST1_TAC o SYM >> irule MEASURE_CONG >>
    rw[MEASURE_SPACE_DIFF] >> Cases_on `x ∈ r` >> simp[] >> first_x_assum $ qspec_then `x` mp_tac >> simp[]
QED

Theorem MEASURE_SPACE_FINITE_INTER:
    ∀m E s. FINITE s ∧ s ≠ ∅ ∧ measure_space m ∧ (∀i. i ∈ s ⇒ E i ∈ measurable_sets m) ⇒
        BIGINTER (IMAGE E s) ∈ measurable_sets m
Proof
    simp[Once $ GSYM AND_IMP_INTRO] >> NTAC 2 gen_tac >> Induct_on `s` >> rw[] >>
    Cases_on `s = ∅` >> simp[] >> fs[] >> irule MEASURE_SPACE_INTER >> simp[]
QED

Definition finite_def:
    finite m ⇔ measure m (m_space m) < +∞
End

Definition finite_measure_space_def:
    finite_measure_space m ⇔ measure_space m ∧ finite m
End

Theorem finite_measure_space_sigma_finite:
    ∀m. finite_measure_space m ⇒ sigma_finite_measure_space m
Proof
    rw[finite_measure_space_def,sigma_finite_measure_space_def,finite_def,sigma_finite_def] >>
    qexists_tac `K (m_space m)` >> simp[FUNSET,MEASURE_SPACE_SPACE,EXTENSION,IN_BIGUNION_IMAGE]
QED

Theorem sigma_finite_measure_space_measure_space:
    ∀m. sigma_finite_measure_space m ⇒ measure_space m
Proof
    simp[sigma_finite_measure_space_def]
QED

Theorem measure_space_cong:
    ∀sp sts mu nu. measure_space (sp,sts,mu) ∧ (∀s. s ∈ sts ⇒ nu s = mu s) ⇒
         measure_space (sp,sts,nu)
Proof
    rw[measure_space_def,positive_def,countably_additive_def]
    >- (`∅ ∈ sts` suffices_by rw[] >> drule SIGMA_ALGEBRA_EMPTY >> simp[])
    >- (irule ext_suminf_eq >> rw[] >> first_x_assum $ irule o GSYM >> fs[FUNSET])
QED

Theorem finite_measure_space_cong:
    ∀sp sts mu nu. finite_measure_space (sp,sts,mu) ∧ (∀s. s ∈ sts ⇒ nu s = mu s) ⇒
         finite_measure_space (sp,sts,nu)
Proof
    rw[finite_measure_space_def]
    >- (irule measure_space_cong >> qexists_tac `mu` >> simp[])
    >- (fs[finite_def] >> `sp ∈ sts` suffices_by rw[] >>
        drule MEASURE_SPACE_MSPACE_MEASURABLE >> simp[])
QED

Theorem finite_measure_space_measure_not_infty:
    ∀m s. finite_measure_space m ∧ s ∈ measurable_sets m ⇒
        measure m s ≠ −∞ ∧ measure m s ≠ +∞
Proof
    rw[finite_measure_space_def,finite_def,lt_infty]
    >- (fs[measure_space_def,positive_def] >> last_x_assum $ dxrule_then assume_tac >>
        irule lte_trans >> qexists_tac `Normal 0` >> simp[extreal_lt_simp,normal_0])
    >- (irule let_trans >> qexists_tac `measure m (m_space m)` >> simp[] >> irule INCREASING >>
        simp[MEASURE_SPACE_INCREASING,MEASURE_SPACE_MSPACE_MEASURABLE,MEASURABLE_SETS_SUBSET_SPACE])
QED

Theorem measure_space_fixed_state_measure:
    ∀sa x. sigma_algebra sa ⇒ measure_space (space sa,subsets sa,C 𝟙 x)
Proof
    simp[measure_space_def,positive_def,countably_additive_def,
        m_space_def,measurable_sets_def,measure_def,indicator_fn_def] >>
    rw[] >> rw[] >> fs[]
    >- (rename [`x ∈ f n`] >>
        `(C 𝟙 x ∘ f) = (λi. if i = n then 1 else 0:extreal)` suffices_by rw[ext_suminf_sing_general] >>
        rw[FUN_EQ_THM,o_DEF,indicator_fn_def] >> Cases_on `i = n` >> simp[] >>
        last_x_assum (qspecl_then [`i`,`n`] assume_tac) >> rfs[DISJOINT_DEF,EXTENSION] >>
        pop_assum $ qspec_then `x` assume_tac >> rfs[])
    >- (irule ext_suminf_zero >> rw[indicator_fn_def] >> first_x_assum $ qspec_then `f n` assume_tac >>
        rfs[] >> first_x_assum $ qspec_then `n` assume_tac >> fs[])
QED

Theorem finite_measure_space_fixed_state_measure:
    ∀sa x. sigma_algebra sa ⇒ finite_measure_space (space sa,subsets sa,C 𝟙 x)
Proof
    rw[finite_measure_space_def,measure_space_fixed_state_measure,finite_def,indicator_fn_def]
QED

Theorem sigma_finite_measure_space_fixed_state_measure:
    ∀sa x. sigma_algebra sa ⇒ sigma_finite_measure_space (space sa,subsets sa,C 𝟙 x)
Proof
    simp[finite_measure_space_fixed_state_measure,finite_measure_space_sigma_finite]
QED

Theorem measure_space_add:
    ∀sa mu nu mnu. measure_space (space sa,subsets sa,mu) ∧
        measure_space (space sa,subsets sa,nu) ∧
        (∀s. s ∈ subsets sa ⇒ mnu s = mu s + nu s) ⇒
        measure_space (space sa,subsets sa,mnu)
Proof
    rw[measure_space_def,positive_def,countably_additive_def,m_space_def,measurable_sets_def,measure_def]
    >- (dxrule_then assume_tac $ SIGMA_ALGEBRA_EMPTY >> fs[])
    >- (irule le_add >> fs[])
    >- ((qspecl_then [`mu ∘ f`,`nu ∘ f`] assume_tac) ext_suminf_add >> rfs[o_DEF,FUNSET])
QED

Theorem measure_space_sum:
    ∀sa mui nu s. FINITE s ∧ sigma_algebra sa ∧
        (∀i. i ∈ s ⇒ measure_space (space sa,subsets sa,mui i)) ∧
        (∀t. t ∈ subsets sa ⇒ nu t = ∑ (C mui t) s) ⇒ measure_space (space sa,subsets sa,nu)
Proof
    `∀(s:β->bool). FINITE s ⇒ ∀(sa:α algebra) mui nu. sigma_algebra sa ∧
        (∀i. i ∈ s ⇒ measure_space (space sa,subsets sa,mui i)) ∧
        (∀t. t ∈ subsets sa ⇒ nu t = ∑ (C mui t) s) ⇒
        measure_space (space sa,subsets sa,nu)` suffices_by (rw[] >>
        last_x_assum $ drule_then assume_tac >> pop_assum $ drule_all_then assume_tac >> simp[]) >>
    Induct_on `s` >> rw[]
    >- (fs[EXTREAL_SUM_IMAGE_EMPTY] >> irule measure_space_cong >>
        qexists_tac `K 0` >> simp[] >> dxrule_then assume_tac measure_space_trivial >>
        fs[sigma_finite_measure_space_def,K_DEF]) >>
    last_x_assum $ qspecl_then [`sa`,`mui`,`λt. ∑ (C mui t) s`] assume_tac >> rfs[] >>
    irule measure_space_add >> qexistsl_tac [`mui e`,`(λt. ∑ (C mui t) s)`] >>
    simp[] >> qx_gen_tac `t` >> rw[] >>
    qspecl_then [`C mui t`,`s`,`e`]
        (fn th => assume_tac th >> rfs[DELETE_NON_ELEMENT_RWT] >> pop_assum irule) $
        SIMP_RULE bool_ss [GSYM RIGHT_FORALL_IMP_THM] EXTREAL_SUM_IMAGE_PROPERTY >>
    DISJ1_TAC >> rw[] >> irule pos_not_neginf >> fs[measure_space_def,positive_def]
QED

Theorem measure_space_cmul:
    ∀sa mu nu c. measure_space (space sa,subsets sa,mu) ∧ 0 ≤ c ∧
        (∀s. s ∈ subsets sa ⇒ nu s = c * mu s) ⇒
        measure_space (space sa,subsets sa,nu)
Proof
    rw[measure_space_def,positive_def,countably_additive_def,m_space_def,measurable_sets_def,measure_def]
    >- (dxrule_then assume_tac $ SIGMA_ALGEBRA_EMPTY >> fs[])
    >- (irule le_mul >> fs[])
    >- ((qspecl_then [`mu ∘ f`,`c`] assume_tac) ext_suminf_cmul >> rfs[o_DEF,FUNSET])
QED

Theorem measure_space_suminf:
    ∀sa mun nu. (∀n. measure_space (space sa,subsets sa,mun n)) ∧
        (∀s. s ∈ subsets sa ⇒ nu s = suminf (C mun s)) ⇒
        measure_space (space sa,subsets sa,nu)
Proof
    rw[measure_space_def,positive_def,countably_additive_def,m_space_def,measurable_sets_def,measure_def] >>
    fs[GSYM RIGHT_AND_FORALL_THM]
    >- (dxrule_then assume_tac $ SIGMA_ALGEBRA_EMPTY >> simp[ext_suminf_0,C_DEF])
    >- (irule ext_suminf_pos >> rw[])
    >- (`suminf (nu ∘ f) = suminf (λi. suminf (C mun (f i)))` by (
            irule ext_suminf_eq >> rw[] >> rfs[FUNSET]) >>
        pop_assum SUBST1_TAC >> simp[C_DEF,o_DEF] >>
        qspec_then `C mun ∘ f` (irule o SIMP_RULE (srw_ss ()) []) ext_suminf_nested >>
        rw[] >> last_x_assum $ irule o cj 2 >> fs[FUNSET])
QED

Theorem finite_measure_space_add:
    ∀sa mu nu mnu. finite_measure_space (space sa,subsets sa,mu) ∧
        finite_measure_space (space sa,subsets sa,nu) ∧
        (∀s. s ∈ subsets sa ⇒ mnu s = mu s + nu s) ⇒
        finite_measure_space (space sa,subsets sa,mnu)
Proof
    rw[] >> simp[finite_measure_space_def,finite_def] >> rw[]
    >- (irule measure_space_add >> qexistsl_tac [`mu`,`nu`] >> fs[finite_measure_space_def]) >>
    `space sa ∈ subsets sa` by (fs[finite_measure_space_def] >>
        dxrule MEASURE_SPACE_MSPACE_MEASURABLE >> simp[]) >>
    fs[GSYM lt_infty] >> NTAC 2 $ dxrule_then assume_tac finite_measure_space_measure_not_infty >>
    rfs[] >> pop_assum (fn th => NTAC 2 $ drule_then assume_tac th) >>
    Cases_on `mu (space sa)` >> Cases_on `nu (space sa)` >> rfs[extreal_add_def]
QED

Theorem finite_measure_space_cmul:
    ∀sa mu nu c. finite_measure_space (space sa,subsets sa,mu) ∧ 0 ≤ c ∧
        (∀s. s ∈ subsets sa ⇒ nu s = Normal c * mu s) ⇒
        finite_measure_space (space sa,subsets sa,nu)
Proof
    rw[] >> simp[finite_measure_space_def,finite_def] >> rw[]
    >- (irule measure_space_cmul >> qexistsl_tac [`Normal c`,`mu`] >> fs[finite_measure_space_def]) >>
    `space sa ∈ subsets sa` by (fs[finite_measure_space_def] >>
        dxrule MEASURE_SPACE_MSPACE_MEASURABLE >> simp[]) >>
    fs[GSYM lt_infty] >> drule_then assume_tac finite_measure_space_measure_not_infty >>
    rfs[] >> pop_assum $ drule_then assume_tac >> Cases_on `mu (space sa)` >> rfs[extreal_mul_def]
QED

(*---------------------------------------------------------------------------*)
(* Trivial stuff for AE *)
(*---------------------------------------------------------------------------*)

Theorem AE_subset:
    ∀m P Q. (AE x::m. P x) ∧ (∀x. x ∈ m_space m ∧ P x ⇒ Q x) ⇒ (AE x::m. Q x)
Proof
    rw[AE_ALT] >> qexists_tac `N` >> fs[SUBSET_DEF] >> rw[] >>
    NTAC 2 $ first_x_assum $ drule_then assume_tac >> gs[]
QED

Theorem AE_eq_add:
    ∀m f fae g gae. measure_space m ∧ (AE x::m. f x = fae x) ∧ (AE x::m. g x = gae x) ⇒
        AE x::m. f x + g x = fae x + gae x
Proof
    rw[] >> fs[AE_ALT] >> qexists_tac `N ∪ N'` >>
    (drule_then assume_tac) NULL_SET_UNION >> rfs[IN_APP] >> pop_assum kall_tac >>
    fs[SUBSET_DEF] >> rw[] >> NTAC 2 (last_x_assum (drule_then assume_tac)) >> 
    CCONTR_TAC >> fs[]
QED

Theorem AE_T:
    ∀m. measure_space m ⇒ AE x::m. T
Proof
    rw[AE_ALT] >> qexists_tac `∅` >> simp[NULL_SET_EMPTY]
QED

Theorem AE_UNION:
    ∀m P Q. measure_space m ∧ ((AE x::m. P x) ∨ (AE x::m. Q x)) ⇒ (AE x::m. P x ∨ Q x)
Proof
    rw[AE_ALT,null_set_def] >> qexists_tac `N` >> fs[SUBSET_DEF]
QED

(* P after s in ∀ *)
Theorem AE_BIGUNION:
    ∀m P s. measure_space m ∧ (∃n. n ∈ s ∧ AE x::m. P n x) ⇒ (AE x::m. ∃n. n ∈ s ∧ P n x)
Proof
    rw[AE_ALT,null_set_def] >> qexists_tac `N` >> fs[SUBSET_DEF,GSYM IMP_DISJ_THM]
QED

Theorem AE_INTER:
    ∀m P Q. measure_space m ∧ (AE x::m. P x) ∧ (AE x::m. Q x) ⇒ (AE x::m. P x ∧ Q x)
Proof
    rw[AE_ALT] >> qexists_tac `N ∪ N'` >> rename [`N ∪ M`] >>
    simp[SIMP_RULE (srw_ss ()) [IN_APP] NULL_SET_UNION] >>
    fs[SUBSET_DEF] >> rw[] >> simp[]
QED

(* P after s in ∀ *)
Theorem AE_BIGINTER:
    ∀m P s. measure_space m ∧ countable s ∧ (∀n. n ∈ s ⇒ AE x::m. P n x) ⇒ (AE x::m. ∀n. n ∈ s ⇒ P n x)
Proof
    rw[AE_ALT] >> fs[GSYM RIGHT_EXISTS_IMP_THM,SKOLEM_THM] >> qexists_tac `BIGUNION (IMAGE f s)` >>
    rename [`IMAGE N s`] >> REVERSE CONJ_TAC
    >- (fs[SUBSET_DEF] >> rw[] >> NTAC 2 (first_x_assum $ drule_then assume_tac >> rfs[]) >>
        map_every (fn qex => qexists_tac qex >> simp[]) [`N n`,`n`]) >>
    fs[COUNTABLE_ENUM] >- simp[NULL_SET_EMPTY] >> simp[IMAGE_IMAGE] >>
    fs[null_set_def] >> CONJ_ASM1_TAC >- (irule_at Any MEASURE_SPACE_BIGUNION >> simp[]) >>
    simp[GSYM le_antisym] >> irule_at Any $ cj 2 $ iffLR positive_def >> simp[iffLR measure_space_def] >>
    irule leeq_trans >> qexists_tac `suminf (measure m ∘ (N ∘ f))` >>
    irule_at Any $ iffLR countably_subadditive_def >>
    simp[MEASURE_SPACE_COUNTABLY_SUBADDITIVE,FUNSET,o_DEF,ext_suminf_0]
QED

Theorem AE_eq_sum:
    ∀m f fae s. FINITE s ∧ measure_space m ∧ (∀n. n ∈ s ⇒ AE x::m. (f n x):extreal = fae n x) ∧
        ((∀n x. n ∈ s ∧ x ∈ m_space m ⇒ f n x ≠ −∞ ∧ fae n x ≠ −∞) ∨
        (∀n x. n ∈ s ∧ x ∈ m_space m ⇒ f n x ≠ +∞ ∧ fae n x ≠ +∞)) ⇒
        AE x::m. ∑ (C f x) s = ∑ (C fae x) s
Proof
    rw[] >> qspecl_then [`m`,`λn x. f n x = fae n x`,`s`] assume_tac AE_BIGINTER >> rfs[finite_countable] >>
    qspecl_then [`m`,`λx. ∀n. n ∈ s ⇒ f n x = fae n x`,`λx. ∑ (C f x) s = ∑ (C fae x) s`]
        (irule o SIMP_RULE (srw_ss ()) []) AE_subset >>
    rw[] >> irule EXTREAL_SUM_IMAGE_EQ >> rw[C_DEF]
QED

(* Transition Kernels *)

Definition transition_kernel_def:
    transition_kernel sa = {p | sigma_algebra sa ∧
        (∀s. s ∈ space sa ⇒ measure_space (space sa,subsets sa,(λA. p s A))) ∧
        (∀A. A ∈ subsets sa ⇒ (λs. p s A) ∈ Borel_measurable sa)}
End

Theorem transition_kernel_alt:
    ∀sa p. p ∈ transition_kernel sa ⇔ sigma_algebra sa ∧
        (∀s. s ∈ space sa ⇒ measure_space (space sa,subsets sa,p s)) ∧
        (∀A. A ∈ subsets sa ⇒ C p A ∈ Borel_measurable sa)
Proof
    simp[transition_kernel_def,C_DEF,GSYM o_DEF,GSYM I_EQ_IDABS] >> simp[o_DEF]
QED

Theorem transition_kernel_imp:
    (∀(sa:α algebra) p. p ∈ transition_kernel sa ⇒ sigma_algebra sa) ∧
    (∀(sa:α algebra) p s. p ∈ transition_kernel sa ∧ s ∈ space sa ⇒
        measure_space (space sa,subsets sa,p s)) ∧
    (∀(sa:α algebra) p A. p ∈ transition_kernel sa ∧ A ∈ subsets sa ⇒
        C p A ∈ Borel_measurable sa)
Proof
    rw[transition_kernel_alt]
QED

Theorem transition_kernel_pos:
    ∀sa p s A. p ∈ transition_kernel sa ∧ s ∈ space sa ∧ A ∈ subsets sa ⇒ 0 ≤ p s A
Proof
    rw[transition_kernel_alt] >> fs[measure_space_def,positive_def]
QED

Theorem transition_kernel_EMPTY:
    ∀sa p s. p ∈ transition_kernel sa ∧ s ∈ space sa ⇒ p s ∅ = 0
Proof
    rw[transition_kernel_alt] >> fs[measure_space_def,positive_def]
QED

Theorem transition_kernel_indicator:
    ∀sa p. sigma_algebra sa ∧ (∀s A. s ∈ space sa ∧ A ∈ subsets sa ⇒ p s A = 𝟙 A s) ⇒
        p ∈ transition_kernel sa
Proof
    rw[transition_kernel_alt]
    >- (irule measure_space_cong >> qexists_tac `C 𝟙 s` >> simp[] >>
        dxrule_then assume_tac measure_space_fixed_state_measure >> simp[])
    >- (irule IN_MEASURABLE_BOREL_INDICATOR >> simp[] >> qexists_tac `A` >> simp[])
QED

Theorem transition_kernel_add:
    ∀sa p q r. p ∈ transition_kernel sa ∧ q ∈ transition_kernel sa ∧
        (∀s A. s ∈ space sa ∧ A ∈ subsets sa ⇒ r s A = p s A + q s A) ⇒
        r ∈ transition_kernel sa
Proof
    rw[transition_kernel_alt]
    >- (irule measure_space_add >> qexistsl_tac [`p s`,`q s`] >> simp[])
    >- (irule IN_MEASURABLE_BOREL_ADD' >> simp[] >> qexistsl_tac [`C p A`,`C q A`] >> simp[])
QED

Theorem transition_kernel_cmul:
    ∀sa p q c. p ∈ transition_kernel sa ∧ 0 ≤ c ∧
        (∀s A. s ∈ space sa ∧ A ∈ subsets sa ⇒ q s A = Normal c * p s A) ⇒
        q ∈ transition_kernel sa
Proof
    rw[transition_kernel_alt]
    >- (irule measure_space_cmul >> qexistsl_tac [`Normal c`,`p s`] >> simp[])
    >- (irule IN_MEASURABLE_BOREL_CMUL >> simp[] >> qexistsl_tac [`C p A`,`c`] >> simp[])
QED

Theorem transition_kernel_suminf:
    ∀sa pn q. (∀n. pn n ∈ transition_kernel sa) ∧
        (∀s A. s ∈ space sa ∧ A ∈ subsets sa ⇒ q s A = suminf (λn. pn n s A)) ⇒
        q ∈ transition_kernel sa
Proof
    rw[transition_kernel_alt]
    >- (irule measure_space_suminf >> qexists_tac `C pn s` >> simp[C_DEF])
    >- (irule IN_MEASURABLE_BOREL_SUMINF >> simp[] >> qexists_tac `λn. C (pn n) A` >> rw[] >>
        fs[measure_space_def,positive_def])
QED

Definition bounded_transition_kernel_def:
    bounded_transition_kernel sa = {p | sigma_algebra sa ∧
        (∀s. s ∈ space sa ⇒ finite_measure_space (space sa,subsets sa,(λA. p s A))) ∧
        (∀A. A ∈ subsets sa ⇒ (λs. p s A) ∈ bounded_Borel_measurable sa)}
End

Theorem bounded_transition_kernel_alt:
    ∀sa p. p ∈ bounded_transition_kernel sa ⇔ sigma_algebra sa ∧
        (∀s. s ∈ space sa ⇒ finite_measure_space (space sa,subsets sa,p s)) ∧
        (∀A. A ∈ subsets sa ⇒ C p A ∈ bounded_Borel_measurable sa)
Proof
    simp[bounded_transition_kernel_def,C_DEF,GSYM o_DEF,GSYM I_EQ_IDABS] >> simp[o_DEF]
QED

Theorem bounded_transition_kernel_transition_kernel:
    ∀sa p. p ∈ bounded_transition_kernel sa ⇒ p ∈ transition_kernel sa
Proof
    simp[bounded_transition_kernel_alt,transition_kernel_alt,
        finite_measure_space_def,IN_BOUNDED_BOREL_MEASURABLE]
QED

Theorem bounded_transition_kernel_alt_bounds:
    ∀sa p. p ∈ bounded_transition_kernel sa ⇔ p ∈ transition_kernel sa ∧
        ∃ub. ∀s A. s ∈ space sa ∧ A ∈ subsets sa ⇒ p s A ≤ Normal ub
Proof
    rw[] >> eq_tac >> simp[bounded_transition_kernel_transition_kernel] >>
    simp[bounded_transition_kernel_alt,finite_measure_space_def,IN_BOUNDED_BOREL_MEASURABLE] >>
    simp[finite_def,FUNSET,closed_interval_def] >> simp[iffLR transition_kernel_alt,SF SFY_ss] >> rw[]
    >- (drule_then assume_tac SIGMA_ALGEBRA_SPACE >> first_x_assum $ dxrule_then assume_tac >> fs[] >>
        qexists_tac `b` >> rw[] >> first_x_assum $ drule_then assume_tac >> fs[] >>
        irule le_trans >> qexists_tac `p s (space sa)` >> simp[] >>
        first_x_assum $ dxrule_then assume_tac >> fs[] >>
        drule_then assume_tac measure_upper_bound >> rfs[])
    >- (irule let_trans >> qexists_tac `Normal ub` >> simp[] >> first_x_assum irule >>
        simp[iffLR transition_kernel_alt,SF SFY_ss,SIGMA_ALGEBRA_SPACE])
    >- (qexistsl_tac [`0`,`ub`] >> qx_gen_tac `s` >> rw[normal_0] >>
        qspec_then `space sa,subsets sa,p s` (irule o SIMP_RULE (srw_ss ()) []) $
            cj 2 $ iffLR positive_def >>
        qexists_tac `sa` >> simp[iffLR transition_kernel_alt,MEASURE_SPACE_POSITIVE])
QED

Theorem bounded_transition_kernel_alt_bounded_fn:
    ∀sa p. p ∈ bounded_transition_kernel sa ⇔ sigma_algebra sa ∧
        (∀s. s ∈ space sa ⇒ measure_space (space sa,subsets sa,p s)) ∧
        (∀A. A ∈ subsets sa ⇒ C p A ∈ bounded_Borel_measurable sa)
Proof
    rw[bounded_transition_kernel_alt] >> eq_tac >> simp[finite_measure_space_def] >>
    rw[IN_BOUNDED_BOREL_MEASURABLE,finite_def] >> drule_then assume_tac SIGMA_ALGEBRA_SPACE >>
    first_x_assum $ dxrule_then assume_tac >> fs[FUNSET,closed_interval_def] >>
    first_x_assum $ dxrule_then assume_tac >> irule let_trans >> qexists_tac `Normal b` >> fs[]
QED

Theorem bounded_transition_kernel_pos:
    ∀sa p s A. p ∈ bounded_transition_kernel sa ∧ s ∈ space sa ∧ A ∈ subsets sa ⇒ 0 ≤ p s A
Proof
    rw[bounded_transition_kernel_alt,finite_measure_space_def] >>
    fs[measure_space_def,positive_def]
QED

Theorem bounded_transition_kernel_add:
    ∀sa p q r. p ∈ bounded_transition_kernel sa ∧ q ∈ bounded_transition_kernel sa ∧
        (∀s A. s ∈ space sa ∧ A ∈ subsets sa ⇒ r s A = p s A + q s A) ⇒
        r ∈ bounded_transition_kernel sa
Proof
    rw[bounded_transition_kernel_alt]
    >- (irule finite_measure_space_add >> qexistsl_tac [`p s`,`q s`] >> simp[])
    >- (irule IN_BOUNDED_BOREL_MEASURABLE_ADD >> qexistsl_tac [`C p A`,`C q A`] >> simp[])
QED

Theorem bounded_transition_kernel_cmul:
    ∀sa p q c. p ∈ bounded_transition_kernel sa ∧ 0 ≤ c ∧
        (∀s A. s ∈ space sa ∧ A ∈ subsets sa ⇒ q s A = Normal c * p s A) ⇒
        q ∈ bounded_transition_kernel sa
Proof
    rw[bounded_transition_kernel_alt]
    >- (irule finite_measure_space_cmul >> qexistsl_tac [`c`,`p s`] >> simp[])
    >- (irule IN_BOUNDED_BOREL_MEASURABLE_CMUL >> qexistsl_tac [`c`,`C p A`] >> simp[])
QED

(*---------------------------------------------------------------------------*)
(* Trivial stuff for Integrals *)
(*---------------------------------------------------------------------------*)

Theorem pos_fn_integral_fn_plus_not_infty:
    ∀m f. measure_space m ⇒ ∫⁺ m f⁺ ≠ −∞
Proof
    rw[] >> (dxrule_then assume_tac) pos_fn_integral_pos >>
    pop_assum (qspec_then `f⁺` assume_tac) >> CCONTR_TAC >> fs[FN_PLUS_POS]
QED

Theorem pos_fn_integral_fn_minus_not_infty:
    ∀m f. measure_space m ⇒ ∫⁺ m f⁻ ≠ −∞
Proof
    rw[] >> (dxrule_then assume_tac) pos_fn_integral_pos >>
    pop_assum (qspec_then `f⁻` assume_tac) >> CCONTR_TAC >> fs[FN_MINUS_POS]
QED

Theorem pos_fn_integral_not_infty:
    ∀m f. measure_space m ∧ (∀x. x ∈ m_space m ⇒ 0 ≤ f x) ⇒ ∫⁺ m f ≠ −∞
Proof
    rw[] >> (dxrule_then assume_tac) pos_fn_integral_pos >>
    pop_assum (qspec_then `f` assume_tac) >> CCONTR_TAC >> gs[]
QED

Theorem pos_fn_integral_cmul_indicator':
    ∀m s c.  measure_space m ∧ s ∈ measurable_sets m ∧ 0 ≤ c ⇒ ∫⁺ m (λx. c * 𝟙 s x) = c * measure m s
Proof
    rw[] >> Cases_on `c` >> fs[pos_fn_integral_cmul_indicator,pos_fn_integral_cmul_infty]
QED

Theorem pos_fn_integral_cmult_clean:
    ∀m f c. measure_space m ∧ f ∈ Borel_measurable (sig_alg m) ∧
        (∀x. x ∈ m_space m ⇒ 0 ≤ f x) ∧ 0 ≤ c ⇒ ∫⁺ m (λx. c * f x) = c * ∫⁺ m f
Proof
    rw[] >> qspecl_then [`f`,`c`,`m`] mp_tac pos_fn_integral_cmult >> simp[] >>
    qmatch_abbrev_tac `icfp = cifp ⇒ icf = cif` >> `icfp = icf ∧ cifp = cif` suffices_by simp[] >>
    UNABBREV_ALL_TAC >> irule_at Any pos_fn_integral_cong >> csimp[le_mul] >>
    irule IRULER >> irule pos_fn_integral_cong >> simp[]
QED

Theorem pos_simple_fn_change_measure:
    ∀sp sts mu nu f s e a. pos_simple_fn (sp,sts,mu) f s e a ⇒ pos_simple_fn (sp,sts,nu) f s e a
Proof
    simp[pos_simple_fn_def]
QED

Theorem pos_fn_integrable:
    ∀m f. measure_space m ∧ f ∈ Borel_measurable (sig_alg m) ∧
        (∀x. x ∈ m_space m ⇒ 0 ≤ f x) ∧ ∫⁺ m f ≠ +∞ ⇒ integrable m f
Proof
    rw[integrable_def]
    >- (`∫⁺ m f⁺ = ∫⁺ m f` suffices_by simp[] >> irule pos_fn_integral_cong >>
        CONJ_ASM1_TAC >- rw[fn_plus_def] >> simp[])
    >- (`∫⁺ m f⁻ = (Normal 0)` suffices_by simp[] >> simp[normal_0] >>
        drule_then assume_tac pos_fn_integral_zero >> pop_assum $ SUBST1_TAC o SYM >>
        irule pos_fn_integral_cong >> simp[FN_MINUS_POS,fn_minus_def])
QED

Theorem integrable_measurable:
    ∀m f. integrable m f ⇒ f ∈ Borel_measurable (sig_alg m)
Proof
    simp[integrable_def]
QED

Theorem integrable_bounded_Borel_measurable:
    ∀m f. finite_measure_space m ∧ f ∈ bounded_Borel_measurable (sig_alg m) ⇒
        integrable m f
Proof
    rw[] >> irule integrable_bounded >> fs[finite_measure_space_def,IN_BOUNDED_BOREL_MEASURABLE] >>
    qexists_tac `λx. max (abs (Normal a)) (abs (Normal b))` >> REVERSE (rw[])
    >- (simp[extreal_abs_def,max_normal] >> irule integrable_const >> fs[finite_def]) >>
    fs[FUNSET,closed_interval_def] >> first_x_assum (dxrule_then assume_tac) >> fs[] >>
    Cases_on `f x` >> fs[extreal_abs_def] >> pop_assum kall_tac >> simp[le_max]
QED

(* AE stuff *)

Theorem pos_fn_integrable_AE_finite:
    ∀m f. measure_space m ∧ (∀x. x ∈ m_space m ⇒ 0 ≤ f x) ∧
        f ∈ Borel_measurable (m_space m,measurable_sets m) ∧ ∫⁺ m f ≠ +∞ ⇒
        AE x::m. f x = (Normal ∘ real ∘ f) x
Proof
    rw[] >> rw[AE_ALT] >> qexists_tac `{x | x ∈ m_space m ∧ f x = +∞}` >>
    simp[pos_fn_integral_infty_null] >> rw[SUBSET_DEF] >>
    Cases_on `f x` >> fs[normal_real] >> rw[] >>
    last_x_assum (dxrule_then assume_tac) >> rfs[]
QED

Theorem integrable_AE_finite:
    ∀m f. measure_space m ∧ integrable m f ⇒ AE x::m. f x = (Normal ∘ real ∘ f) x
Proof
    rw[] >> fs[integrable_def] >>
    map_every (fn tm => (qspecl_then [`m`,tm] assume_tac) pos_fn_integrable_AE_finite) [`f⁺`,`f⁻`] >>
    rfs[FN_PLUS_POS,FN_MINUS_POS,IN_MEASURABLE_BOREL_FN_PLUS,IN_MEASURABLE_BOREL_FN_MINUS] >>
    fs[AE_ALT] >> qexists_tac `N ∪ N'` >> (drule_then assume_tac) NULL_SET_UNION >>
    rfs[IN_APP] >> pop_assum kall_tac >> fs[SUBSET_DEF] >> rw[] >>
    NTAC 2 (last_x_assum (drule_then assume_tac)) >> Cases_on `f x` >> rw[] >>
    DISJ2_TAC >> first_x_assum irule >> simp[fn_minus_def,extreal_ainv_def]
QED

Theorem integrable_cong_AE:
    ∀m f g. measure_space m ∧ (AE x::m. f x = g x) ∧ integrable m f ∧
        g ∈ Borel_measurable (m_space m,measurable_sets m) ⇒ integrable m g
Proof
    simp[integrable_def] >> NTAC 4 strip_tac >>
    `∫⁺ m f⁺ = ∫⁺ m g⁺ ∧ ∫⁺ m f⁻ = ∫⁺ m g⁻` suffices_by (rw[] >> fs[]) >>
    rw[] >> irule pos_fn_integral_cong_AE >> simp[FN_PLUS_POS,FN_MINUS_POS] >>
    fs[AE_ALT,SUBSET_DEF] >> qexists_tac `N` >> rw[] >>
    last_x_assum (dxrule_then assume_tac) >> pop_assum irule >>
    pop_assum mp_tac >> CONV_TAC CONTRAPOS_CONV >>
    simp[fn_plus_def,fn_minus_def]
QED

Theorem integrable_AE_bounded_Borel_measurable:
    ∀m f a b. finite_measure_space m ∧ f ∈ Borel_measurable (sig_alg m) ∧
        (AE x::m. Normal a ≤ f x ∧ f x ≤ Normal b) ⇒ integrable m f
Proof
    rw[finite_measure_space_def] >> irule integrable_cong_AE >> simp[] >>
    fs[AE_ALT] >> qexists_tac `λx. f x * 𝟙 ((m_space m) DIFF N) x` >>
    irule_at Any integrable_bounded_Borel_measurable >> qexists_tac `N` >>
    simp[finite_measure_space_def,bounded_Borel_measurable_def] >>
    irule_at Any IN_MEASURABLE_BOREL_MUL_INDICATOR >> qexistsl_tac [`max 0 b`,`min 0 a`] >>
    fs[null_set_def,SUBSET_DEF] >> simp[MEASURE_SPACE_COMPL,FUNSET,closed_interval_def] >>
    simp[GSYM AND_IMP_INTRO,GSYM FORALL_IMP_CONJ_THM] >> NTAC 2 strip_tac >>
    last_x_assum $ qspec_then `x` assume_tac >> rfs[] >>
    simp[indicator_fn_def] >> Cases_on `x ∈ N` >> fs[]
    >- simp[REAL_MIN_LE,REAL_LE_MAX]
    >- simp[GSYM max_alt,GSYM min_alt,min_le,le_max]
QED

Theorem integral_mono_AE:
    ∀m f g. measure_space m ∧ (AE x::m. f x ≤ g x) ⇒ ∫ m f ≤ ∫ m g
Proof
    rw[integral_def] >> irule sub_le_sub_imp >> NTAC 2 $ irule_at Any pos_fn_integral_mono_AE >>
    simp[FN_PLUS_POS,FN_MINUS_POS] >>
    map_every (fn tms => qspecl_then tms (irule_at Any o SIMP_RULE (srw_ss ()) []) AE_subset)
        [[`m`,`λx. f x ≤ g x`,`λx. f⁺ x ≤ g⁺ x`],[`m`,`λx. f x ≤ g x`,`λx. g⁻ x ≤ f⁻ x`]] >>
    simp[GSYM FORALL_IMP_CONJ_THM] >> NTAC 2 strip_tac >>
    rw[fn_plus_def,fn_minus_def]
    >| [simp[le_neg],simp[Once le_negl],simp[Once le_negr,le_lt],simp[],simp[le_lt]] >>
    `F` suffices_by simp[] >> qpat_x_assum `¬b` mp_tac >> simp[]
    >- (irule let_trans >> qexists_tac `g x` >> simp[])
    >- (irule lte_trans >> qexists_tac `f x` >> simp[])
QED

(* better stuff *)

Theorem integrable_mul_indicator':
    ∀m s f. measure_space m ∧ s ∈ measurable_sets m ∧ integrable m f ⇒
        integrable m (λx. f x * 𝟙 s x)
Proof
    rw[integrable_def,lt_infty] >- (irule IN_MEASURABLE_BOREL_MUL_INDICATOR >> simp[]) >>
    irule let_trans >| [qexists_tac `∫⁺ m f⁺`,qexists_tac `∫⁺ m f⁻`] >>
    simp[fn_plus_mul_indicator,fn_minus_mul_indicator] >> irule pos_fn_integral_mono >>
    simp[GSYM FORALL_IMP_CONJ_THM] >> NTAC 2 strip_tac >> irule_at Any le_mul >>
    rw[indicator_fn_def] >> simp[FN_PLUS_POS,FN_MINUS_POS]
QED

(* rename prime or clean *)
Theorem integral_add_pure:
    ∀m f g. measure_space m ∧ integrable m f ∧ integrable m g ⇒
        ∫ m (λx. f x + g x) = ∫ m f + ∫ m g
Proof
    rw[] >> imp_res_tac integrable_AE_finite >>
    (qspecl_then [`m`,`f`,`Normal ∘ real ∘ f`,`g`,`Normal ∘ real ∘ g`] assume_tac)
        AE_eq_add >> rfs[] >>
    map_every (fn tms => (qspecl_then tms assume_tac) integral_cong_AE)
        [[`m`,`f`,`Normal ∘ real ∘ f`],[`m`,`g`,`Normal ∘ real ∘ g`],
        [`m`,`(λx. f x + g x)`,`(λx. Normal (real (f x)) + Normal (real (g x)))`]] >>
    rfs[] >> NTAC 3 (pop_assum kall_tac) >>
    qspecl_then [`m`,`Normal ∘ real ∘ f`,`Normal ∘ real ∘ g`] assume_tac integral_add >>
    rfs[] >> pop_assum irule >> rw[] >> irule integrable_cong_AE >> fs[integrable_def] >>
    simp[IN_MEASURABLE_BOREL_NORMAL_REAL]
    >| [qexists_tac `f`,qexists_tac `g`] >> simp[]
QED

Theorem integrable_add_pure:
    ∀m f g. measure_space m ∧ integrable m f ∧ integrable m g ⇒ integrable m (λx. f x + g x)
Proof
    rw[] >> imp_res_tac integrable_AE_finite >>
    (qspecl_then [`m`,`f`,`Normal ∘ real ∘ f`,`g`,`Normal ∘ real ∘ g`] assume_tac) AE_eq_add >> rfs[] >>
    map_every (fn tms => (qspecl_then tms assume_tac) integrable_cong_AE)
        [[`m`,`f`,`Normal ∘ real ∘ f`],[`m`,`g`,`Normal ∘ real ∘ g`],
        [`m`,`(λx. Normal (real (f x)) + Normal (real (g x)))`,`(λx. f x + g x)`]] >>
    rfs[integrable_measurable,IN_MEASURABLE_BOREL_NORMAL_REAL] >> pop_assum irule >>
    simp[Once EQ_SYM_EQ] >> irule_at Any IN_MEASURABLE_BOREL_ADD' >>
    qexistsl_tac [`g`,`f`] >> simp[integrable_measurable] >>
    qspecl_then [`m`,`Normal ∘ real ∘ f`,`Normal ∘ real ∘ g`] (irule o SIMP_RULE (srw_ss ()) []) integrable_add >>
    simp[]
QED

Theorem integral_sum_pure:
    ∀m f s. FINITE s ∧ measure_space m ∧ (∀i. i ∈ s ⇒ integrable m (f i)) ⇒
        ∫ m (λx. ∑ (λi. f i x) s) = ∑ (λi. ∫ m (f i)) s
Proof
    rw[] >>
    resolve_then Any (resolve_then (Pos $ el 2)
        (qspecl_then [`zzz`,`xxx`,`s`,`m`,`λi. Normal ∘ real ∘ f i`] irule) integral_sum) EQ_TRANS EQ_TRANS >>
    qexistsl_tac [`f`,`m`,`s`] >> simp[] >>
    first_assum $ C (resolve_then Any assume_tac) integrable_AE_finite >> rfs[] >>
    qspecl_then [`m`,`λi x. f i x = Normal (real (f i x))`,`s`] assume_tac AE_BIGINTER >>
    rfs[finite_countable] >> rw[]
    >- (irule integrable_cong_AE >> simp[integrable_measurable,IN_MEASURABLE_BOREL_NORMAL_REAL] >>
        qexists_tac `f i` >> simp[])
    >- (irule integral_cong_AE >> simp[] >>
        qspecl_then [`m`,`λx. ∀n. n ∈ s ⇒ f n x = Normal (real (f n x))`,
            `λx. ∑ (λi. f i x) s = ∑ (λi. Normal (real (f i x))) s`]
            (irule o SIMP_RULE (srw_ss ()) []) AE_subset >>
        rw[] >> irule EXTREAL_SUM_IMAGE_EQ >> csimp[] >> DISJ1_TAC >> rw[] >>
        first_x_assum $ dxrule_then SUBST1_TAC >> simp[])
    >- (irule EXTREAL_SUM_IMAGE_EQ >> simp[] >>
        `∀i. i ∈ s ⇒ ∫ m (Normal ∘ real ∘ f i) = ∫ m (f i)` by (rw[] >> irule integral_cong_AE >>
            simp[Once EQ_SYM_EQ]) >>
        simp[integrable_finite_integral])
QED

Theorem integrable_sum_pure:
    ∀m f s. FINITE s ∧ measure_space m ∧ (∀i. i ∈ s ⇒ integrable m (f i)) ⇒
        integrable m (λx. ∑ (λi. f i x) s)
Proof
    rw[] >> irule_at Any integrable_cong_AE >> simp[] >> drule_then (irule_at Any) IN_MEASURABLE_BOREL_SUM' >>
    qexistsl_tac [`f`,`λx. ∑ (λi. Normal (real (f i x))) s`] >> simp[integrable_measurable] >>
    qspecl_then [`m`,`λi. Normal ∘ real ∘ f i`,`s`] (irule_at Any o SIMP_RULE (srw_ss ()) []) integrable_sum >>
    simp[] >> first_assum $ C (resolve_then Any assume_tac) integrable_AE_finite >> rfs[] >>
    qspecl_then [`m`,`λi x. f i x = Normal (real (f i x))`,`s`] assume_tac AE_BIGINTER >>
    rfs[finite_countable] >> rw[]
    >- (irule integrable_cong_AE >> simp[integrable_measurable,IN_MEASURABLE_BOREL_NORMAL_REAL] >>
        qexists_tac `f i` >> simp[])
    >- (qspecl_then [`m`,`λx. ∀n. n ∈ s ⇒ f n x = Normal (real (f n x))`,
            `λx. ∑ (λi. Normal (real (f i x))) s = ∑ (λi. f i x) s`]
            (irule o SIMP_RULE (srw_ss ()) []) AE_subset >>
        rw[] >> irule EQ_SYM >> irule EXTREAL_SUM_IMAGE_EQ >> csimp[] >>
        DISJ1_TAC >> rw[] >> first_x_assum $ dxrule_then SUBST1_TAC >> simp[])
QED

Theorem integrable_sub_gen:
    ∀m f g. measure_space m ∧ integrable m f ∧ integrable m g ∧
        (∀x. x ∈ m_space m ⇒ f x ≠ −∞ ∧ g x ≠ +∞ ∨ f x ≠ +∞ ∧ g x ≠ −∞) ⇒
        integrable m (λx. f x - g x)
Proof
    rw[] >> (drule_then assume_tac) integrable_cmul >>
    pop_assum (dxrule_then assume_tac) >> pop_assum (qspec_then `-1` assume_tac) >>
    (qspecl_then [`m`,`f`,`(λx. Normal (-1) * g x)`] assume_tac) integrable_add >>
    rfs[normal_minus1,GSYM neg_minus1] >>
    `(∀x. x ∈ m_space m ⇒ f x ≠ −∞ ∧ -g x ≠ −∞ ∨ f x ≠ +∞ ∧ -g x ≠ +∞)` by (
        rw[] >> last_x_assum (dxrule_then assume_tac) >> fs[] >>
        Cases_on `g x` >> fs[extreal_ainv_def]) >>
    fs[] >> pop_assum kall_tac >> irule integrable_eq >> simp[] >>
    qexists_tac `(λx. f x + -g x)` >> rw[] >> irule (GSYM extreal_sub_add) >> rw[]
QED

(* rename prime or clean *)
Theorem integral_sub_pure:
    ∀m f g. measure_space m ∧ integrable m f ∧ integrable m g ⇒
        ∫ m (λx. f x - g x) = ∫ m f - ∫ m g
Proof
    rw[] >>
    map_every (fn th => (qspecl_then [`m`,`g`,`-1`] assume_tac) th)
        [integral_cmul,integrable_cmul] >>
    rfs[normal_minus1,GSYM neg_minus1] >>
    (qspecl_then [`m`,`f`,`(λx. -g x)`] assume_tac) integral_add_pure >> rfs[] >>
    `∫ m f − ∫ m g = ∫ m f + -∫ m g ∧
        ∫ m (λx. f x − g x) = ∫ m (λx. f x + -g x)` suffices_by rw[] >>
    NTAC 3 (pop_assum kall_tac) >> rw[]
    >- (irule extreal_sub_add >> simp[integrable_finite_integral]) >>
    irule integral_cong_AE >> simp[] >> imp_res_tac integrable_AE_finite >>
    fs[AE_ALT] >> qexists_tac `N ∪ N'` >> (drule_then assume_tac) NULL_SET_UNION >>
    rfs[IN_APP] >> pop_assum kall_tac >> fs[SUBSET_DEF] >> rw[] >>
    pop_assum mp_tac >> CONV_TAC CONTRAPOS_CONV >> rw[] >>
    NTAC 2 (last_x_assum (drule_then assume_tac)) >> rfs[] >>
    irule extreal_sub_add >> Cases_on `f x` >> Cases_on `g x` >> fs[]
QED

(* Density *)

Theorem m_space_density:
    ∀m f. m_space (density m f) = m_space m
Proof
    simp[density_def]
QED

val _ = mk_local_simp "m_space_density";

Theorem measurable_sets_density:
    ∀m f. measurable_sets (density m f) = measurable_sets m
Proof
    simp[density_def]
QED

val _ = mk_local_simp "measurable_sets_density";

Theorem sig_alg_density:
    ∀m f. sig_alg (density m f) = sig_alg m
Proof
    simp[density_def]
QED

val _ = mk_local_simp "sig_alg_density";

Theorem pos_fn_integral_cong_gen:
    ∀sp sts mu nu f g. (measure_space (sp,sts,mu) ∨ measure_space (sp,sts,nu)) ∧
        (∀s. s ∈ sts ⇒ mu s = nu s) ∧ (∀x. x ∈ sp ⇒ 0 ≤ f x ∨ 0 ≤ g x) ∧ (∀x. x ∈ sp ⇒ f x = g x) ⇒
        ∫⁺ (sp,sts,mu) f = ∫⁺ (sp,sts,nu) g
Proof
    rw[] >> irule EQ_TRANS >> qexists_tac `∫⁺ (sp,sts,nu) f` >>
    irule_at Any pos_fn_integral_cong_measure >> irule_at Any pos_fn_integral_cong >> fs[] >>
    dxrule_then irule measure_space_cong >> simp[]
QED

Theorem pos_fn_integral_density_clean:
    ∀m f g. measure_space m ∧ f ∈ Borel_measurable (sig_alg m) ∧
        g ∈ Borel_measurable (sig_alg m) ∧
        (∀x. x ∈ m_space m ⇒ 0 ≤ f x) ∧ (∀x. x ∈ m_space m ⇒ 0 ≤ g x) ⇒
        ∫⁺ (density m f) g = ∫⁺ m (λx. f x * g x)
Proof
    rw[] >> qspecl_then [`m`,`f`,`λx. g x * 𝟙 (m_space m) x`] assume_tac pos_fn_integral_density >> rfs[] >>
    `∫⁺ (density m f⁺) (λx. g x * 𝟙 (m_space m) x) = ∫⁺ (density m f) g` by (
        `measure_space (density m f) ∧ measure_space (density m f⁺)` by
            simp[measure_space_density,measure_space_density'] >>
        fs[density_def,density_measure_def] >> irule pos_fn_integral_cong_gen >>
        rw[indicator_fn_def] >> irule pos_fn_integral_cong >> rw[]) >>
    `∫⁺ m (λx. f⁺ x * (g x * 𝟙 (m_space m) x)) = ∫⁺ m (λx. f x * g x)` by (
        irule pos_fn_integral_cong >> rw[] >> simp[indicator_fn_def] >> irule le_mul >> simp[]) >>
    NTAC 2 $ pop_assum SUBST_ALL_TAC >> pop_assum irule >> rw[]
    >- (rw[indicator_fn_def])
    >- (irule IN_MEASURABLE_BOREL_MUL_INDICATOR >> simp[MEASURE_SPACE_MSPACE_MEASURABLE])
    >- (qspecl_then [`m`,`λx. 0 ≤ f x`] (irule o SIMP_RULE (srw_ss ()) []) FORALL_IMP_AE >> simp[])
QED

Theorem pos_fn_integral_density_cong:
    ∀m f g h. measure_space m ∧ f ∈ Borel_measurable (sig_alg m) ∧
        g ∈ Borel_measurable (sig_alg m) ∧ h ∈ Borel_measurable (sig_alg m) ∧
        (∀x. x ∈ m_space m ⇒ 0 ≤ f x) ∧ (∀x. x ∈ m_space m ⇒ 0 ≤ g x) ∧ (∀x. x ∈ m_space m ⇒ 0 ≤ h x) ∧
        (∀x. x ∈ m_space m ∧ f x ≠ 0 ⇒ g x = h x) ⇒
        ∫⁺ (density m f) g = ∫⁺ (density m f) h
Proof
    rw[] >> simp[pos_fn_integral_density_clean,SF SFY_ss] >> irule pos_fn_integral_cong >>
    simp[le_mul] >> rw[] >> Cases_on `f x = 0` >> simp[]
QED

(* Radon-Nikodym derivatives *)

Definition rn_derivative_def:
    rn_derivative sa mu nu = {f | f ∈ Borel_measurable sa ∧
        (∀x. x ∈ space sa ⇒ 0 ≤ f x) ∧
        (∀s. s ∈ subsets sa ⇒ (f * (space sa,subsets sa,nu)) s = mu s)}
End

Theorem in_rn_derivative:
    ∀sa mu nu f. f ∈ rn_derivative sa mu nu ⇔
        f ∈ Borel_measurable sa ∧ (∀x. x ∈ space sa ⇒ 0 ≤ f x) ∧
        ∀s. s ∈ subsets sa ⇒ (f * (space sa,subsets sa,nu)) s = mu s
Proof
    rw[rn_derivative_def]
QED

Theorem measure_absolutely_continuous_self:
    ∀sa mu. mu ≪ (space sa,subsets sa,mu)
Proof
    simp[measure_absolutely_continuous_def]
QED

Theorem pos_fn_integral_eq_0_imp_AE_0:
    ∀m f. measure_space m ∧ f ∈ Borel_measurable (sig_alg m) ∧ (∀x. x ∈ m_space m ⇒ 0 ≤ f x) ∧
        ∫⁺ m f = 0 ⇒ AE x::m. f x = 0
Proof
    rw[] >>
    qspecl_then [`m`,`λx. ∀n. f x < 1 / &SUC n`,`λx. f x = 0`]
        (irule o SIMP_RULE (srw_ss ()) []) AE_subset >>
    CONJ_TAC
    >- (rw[] >> CCONTR_TAC >> last_x_assum $ dxrule_then assume_tac >> rfs[le_lt] >>
        qpat_x_assum `∀n. _` mp_tac >> simp[extreal_lt_def] >> Cases_on `f x` >> fs[] >>
        simp[extreal_of_num_def,SYM normal_1,extreal_div_def,extreal_inv_def,extreal_mul_def] >>
        rw[] >> qspec_then `1 / r` assume_tac REAL_BIGNUM >> fs[] >> qexists_tac `n - 1` >>
        Cases_on `n` >- rfs[REAL_LT_LDIV_EQ] >> rename [`1 / r < &SUC n`] >> rfs[REAL_LT_LDIV_EQ]) >>
    qspecl_then [`m`,`λn x. f x < 1 / &SUC n`,`𝕌(:num)`] (irule o SIMP_RULE (srw_ss ()) []) AE_BIGINTER >>
    rw[num_countable] >> simp[AE_DEF] >> qexists_tac `{x | ¬(f x < 1 / &SUC n)} ∩ m_space m` >> csimp[] >>
    simp[extreal_lt_def,null_set_def] >> CONJ_ASM1_TAC
    >- (irule $ cj 2 IN_MEASURABLE_BOREL_ALL_MEASURE >> simp[]) >>
    drule_then assume_tac $ cj 2 $ iffLR measure_space_def >>
    drule_all_then assume_tac $ cj 2 $ iffLR positive_def >> qmatch_abbrev_tac `measure _ s = _` >>
    CCONTR_TAC >> pop_assum $ assume_tac o GSYM >> dxrule_all_then assume_tac $ iffRL lt_le >>
    qpat_x_assum `∫⁺ m f = 0` mp_tac >> simp[GSYM le_antisym,GSYM extreal_lt_def] >> DISJ1_TAC >>
    irule lte_trans >> qexists_tac `∫⁺ m (λx. Normal (1 / &SUC n) * 𝟙 s x)` >>
    irule_at Any pos_fn_integral_mono >> simp[pos_fn_integral_cmul_indicator,le_mul,INDICATOR_FN_POS,lt_mul] >>
    rw[] >> fs[SYM normal_1,extreal_of_num_def,extreal_div_def,extreal_inv_def,extreal_mul_def] >>
    fs[normal_0] >> simp[GSYM REAL_INV_1OVER] >> rw[indicator_fn_def,Abbr`s`]
QED

Theorem integral_eq_0_imp_AE_0:
    ∀m f. measure_space m ∧ f ∈ Borel_measurable (sig_alg m) ∧
        (∀s. s ∈ measurable_sets m ⇒ ∫ m (λx. f x * 𝟙 s x) = 0) ⇒
        AE x::m. f x = 0
Proof
    rw[] >>
    qspecl_then [`m`,`λx. f⁺ x = 0 ∧ f⁻ x = 0`,`λx. f x = 0`] (irule o SIMP_RULE (srw_ss ()) []) AE_subset >>
    CONJ_TAC >- (rw[] >> simp[Once FN_DECOMP]) >>
    qspecl_then [`m`,`λx. f⁺ x = 0`,`λx. f⁻ x = 0`] (irule o SIMP_RULE (srw_ss ()) []) AE_INTER >>
    simp[] >> NTAC 2 $ irule_at Any pos_fn_integral_eq_0_imp_AE_0 >>
    drule_then assume_tac $ iffLR IN_MEASURABLE_BOREL_PLUS_MINUS >> simp[FN_PLUS_POS,FN_MINUS_POS] >>
    fs[] >> imp_res_tac IN_MEASURABLE_BOREL_OR >> pop_assum kall_tac >> fs[] >>
    NTAC 2 $ first_x_assum $ qspec_then `0` assume_tac >>
    map_every qabbrev_tac [`s = {x | 0 < f⁺ x} ∩ m_space m`,`t = {x | 0 < f⁻ x} ∩ m_space m`] >>
    RES_TAC >> fs[integral_def,fn_plus_mul_indicator,fn_minus_mul_indicator] >>
    `∫⁺ m (λx. f⁺ x * 𝟙 s x) = ∫⁺ m f⁺ ∧ ∫⁺ m (λx. f⁻ x * 𝟙 s x) = 0 ∧
        ∫⁺ m (λx. f⁺ x * 𝟙 t x) = 0 ∧ ∫⁺ m (λx. f⁻ x * 𝟙 t x) = ∫⁺ m f⁻` suffices_by (strip_tac >> fs[]) >>
    drule_then (SUBST1_TAC o GSYM) pos_fn_integral_zero >>
    NTAC 4 $ irule_at Any pos_fn_integral_cong >> simp[FN_PLUS_POS,FN_MINUS_POS,INDICATOR_FN_POS,le_mul] >>
    NTAC 2 $ pop_assum kall_tac >> rw[indicator_fn_def,Abbr `s`,Abbr `t`]
    >- (qspecl_then [`f`,`x`] mp_tac FN_MINUS_POS >> simp[le_lt])
    >- (fs[fn_plus_def,fn_minus_def] >> Cases_on `f x < 0` >> fs[ineq_imp])
    >- (fs[fn_plus_def,fn_minus_def] >> Cases_on `0 < f x` >> fs[ineq_imp])
    >- (qspecl_then [`f`,`x`] mp_tac FN_PLUS_POS >> simp[le_lt])
QED

Theorem integral_eq_imp_AE_eq:
    ∀m f g. measure_space m ∧ integrable m f ∧ integrable m g ∧
        (∀s. s ∈ measurable_sets m ⇒ ∫ m (λx. f x * 𝟙 s x) = ∫ m (λx. g x * 𝟙 s x)) ⇒
        AE x::m. f x = g x
Proof
    rw[] >>
    qspecl_then [`m`,`λx. f x = (Normal ∘ real ∘ f) x ∧ g x = (Normal ∘ real ∘ g) x ∧
        g x − f x = 0`,`λx. f x = g x`] (irule o SIMP_RULE (srw_ss ()) []) AE_subset >>
    CONJ_TAC >- (rw[] >> Cases_on `f x` >> Cases_on `g x` >> fs[extreal_sub_def]) >>
    qspecl_then [`m`,`λx. f x = Normal (real (f x)) ∧ g x = Normal (real (g x))`,
        `λx. g x - f x = 0`] (irule o SIMP_RULE (srw_ss ()) [GSYM CONJ_ASSOC]) AE_INTER >>
    qspecl_then [`m`,`λx. f x = Normal (real (f x))`,`λx. g x = Normal (real (g x))`]
        (irule_at Any o SIMP_RULE (srw_ss ()) []) AE_INTER >>
    simp[SIMP_RULE (srw_ss ()) [] integrable_AE_finite] >>
    qspecl_then [`m`,`λx. g x - f x`] (irule o SIMP_RULE (srw_ss ()) []) integral_eq_0_imp_AE_0 >>
    irule_at Any IN_MEASURABLE_BOREL_SUB' >> qexistsl_tac [`f`,`g`] >>
    simp[SIMP_RULE (srw_ss ()) [] $ iffLR integrable_def] >> rw[] >>
    map_every (fn tms => qspecl_then tms assume_tac integrable_mul_indicator')
        [[`m`,`s`,`f`],[`m`,`s`,`g`]] >>
    rfs[] >> first_x_assum $ drule_then assume_tac >>
    qspecl_then [`m`,`λx. g x * 𝟙 s x`,`λx. f x * 𝟙 s x`] assume_tac integral_sub_pure >> rfs[] >>
    drule_all_then assume_tac integrable_normal_integral >> fs[] >> pop_assum SUBST_ALL_TAC >>
    fs[extreal_sub_def,normal_0] >> pop_assum $ SUBST1_TAC o SYM >> irule integral_cong >>
    rw[indicator_fn_def]
QED

Theorem rn_derivative_1:
    ∀sa mu. measure_space (space sa,subsets sa,mu) ⇒ (λx. 1) ∈ rn_derivative sa mu mu
Proof
    rw[rn_derivative_def,density_measure_def,IN_MEASURABLE_BOREL_CONST',SF SFY_ss] >>
    qspec_then `𝟙 s` SUBST1_TAC ETA_AX >> drule_then assume_tac pos_fn_integral_indicator >> rfs[]
QED

Theorem rn_derivative_exists:
    ∀sa mu nu. sigma_finite_measure_space (space sa,subsets sa,nu) ∧
        measure_space (space sa,subsets sa,mu) ∧ mu ≪ (space sa,subsets sa,nu) ⇒
        ∃dmdn. dmdn ∈ rn_derivative sa mu nu
Proof
    rw[] >> qspecl_then [`(space sa,subsets sa,nu)`,`mu`] assume_tac Radon_Nikodym' >>
    rfs[sigma_finite_measure_space_def] >> qexists_tac `f` >> simp[in_rn_derivative]
QED

Theorem RN_deriv_exists:
    ∀m v. sigma_finite_measure_space m ∧ measure_space (m_space m,measurable_sets m,v) ∧ v ≪ m ⇒
        v / m ∈ rn_derivative (sig_alg m) v (measure m)
Proof
    rw[] >> simp[RN_deriv_def] >> SELECT_ELIM_TAC >> simp[rn_derivative_def] >>
    fs[sigma_finite_measure_space_def] >> drule_all_then assume_tac Radon_Nikodym' >> rfs[] >>
    qexists_tac `f` >> simp[]
QED

Theorem rn_derivative_change_pos:
    ∀sa mu nu dmdn f. f ∈ Borel_measurable sa ∧ (∀x. x ∈ space sa ⇒ 0 ≤ f x) ∧
        measure_space (space sa,subsets sa,mu) ∧ measure_space (space sa,subsets sa,nu) ∧
        dmdn ∈ rn_derivative sa mu nu ⇒
        ∫⁺ (space sa,subsets sa,mu) f = ∫⁺ (space sa,subsets sa,nu) (λx. dmdn x * f x)
Proof
    rw[] >> fs[rn_derivative_def,measure_absolutely_continuous_def,density_measure_def] >>
    qspecl_then [`(space sa,subsets sa,nu)`,`dmdn`,`f`] assume_tac pos_fn_integral_density_clean >>
    rfs[density_def,density_measure_def] >> pop_assum $ SUBST1_TAC o SYM >>
    irule pos_fn_integral_cong_gen >> simp[]
QED

Theorem rn_derivative_change:
    ∀sa mu nu dmdn f. f ∈ Borel_measurable sa ∧
        measure_space (space sa,subsets sa,mu) ∧ measure_space (space sa,subsets sa,nu) ∧
        dmdn ∈ rn_derivative sa mu nu ⇒
        ∫ (space sa,subsets sa,mu) f = ∫ (space sa,subsets sa,nu) (λx. dmdn x * f x)
Proof
    rw[integral_def] >>
    map_every (fn tms => qspecl_then tms mp_tac rn_derivative_change_pos)
        [[`sa`,`mu`,`nu`,`dmdn`,`f⁺`],[`sa`,`mu`,`nu`,`dmdn`,`f⁻`]] >>
    simp[iffLR IN_MEASURABLE_BOREL_PLUS_MINUS,FN_PLUS_POS,FN_MINUS_POS] >>
    NTAC 2 $ disch_then kall_tac >> fs[rn_derivative_def] >>
    `∀x1:extreal x2 x3 x4. x1 = x3 ∧ x2 = x4 ⇒ x1 - x2 = x3 - x4` by simp[] >>
    pop_assum irule >> NTAC 2 $ irule_at Any pos_fn_integral_cong >> simp[] >>
    `∀x. x ∈ space sa ⇒ ((λx. dmdn x * f x)⁺ x = dmdn x * f⁺ x) ∧ ((λx. dmdn x * f x)⁻ x = dmdn x * f⁻ x)`
        suffices_by simp[FN_PLUS_POS,FN_MINUS_POS,le_mul] >>
    NTAC 2 strip_tac >> simp[FN_PLUS_FFMUL,FN_MINUS_FFMUL]
QED

Theorem rn_derivative_unique:
    ∀sa mu nu f g. sigma_finite_measure_space (space sa,subsets sa,mu) ∧
        measure_space (space sa,subsets sa,nu) ∧
        f ∈ rn_derivative sa mu nu ∧ g ∈ rn_derivative sa mu nu ⇒
        AE x::(space sa,subsets sa,nu). f x = g x
Proof
    rw[sigma_finite_measure_space_def,sigma_finite_def] >> rename [`Ai ∈ (𝕌(:num) → subsets sa)`] >>
    qspecl_then [`(space sa,subsets sa,nu)`,`λx. ∀n. x ∈ Ai n ⇒ f x = g x`,`λx. f x = g x`]
        (irule o SIMP_RULE (srw_ss ()) []) AE_subset >>
    qexists_tac `Ai` >> CONJ_TAC
    >- (rw[] >> qpat_x_assum `_ = space sa` $ SUBST_ALL_TAC o SYM >> rfs[IN_BIGUNION_IMAGE,SF SFY_ss]) >>
    qspecl_then [`(space sa,subsets sa,nu)`,`λn x. x ∈ Ai n ⇒ f x = g x`,`𝕌(:num)`]
        (irule o SIMP_RULE (srw_ss ()) []) AE_BIGINTER >>
    simp[num_countable] >> rw[] >>
    qspecl_then [`(space sa,subsets sa,nu)`,`λx. f x * 𝟙 (Ai n) x = g x * 𝟙 (Ai n) x`,`λx. x ∈ Ai n ⇒ f x = g x`]
        (irule o SIMP_RULE (srw_ss ()) []) AE_subset >>
    CONJ_TAC >- (rw[] >> fs[indicator_fn_def]) >>
    qspecl_then [`m`,`λx. f x * 𝟙 (Ai n) x`,`λx. g x * 𝟙 (Ai n) x`]
        (irule o SIMP_RULE (srw_ss ()) []) integral_eq_imp_AE_eq >>
    fs[rn_derivative_def,density_measure_def,FUNSET] >>
    simp[INDICATOR_FN_POS,le_mul,integrable_pos,integral_pos_fn,
        IN_MEASURABLE_BOREL_MUL_INDICATOR,lt_infty,SF SFY_ss] >>
    rw[] >> `Ai n ∩ s ∈ subsets sa` by simp[SIGMA_ALGEBRA_INTER,SF SFY_ss] >>
    NTAC 2 $ first_x_assum $ drule_then assume_tac >> fs[INDICATOR_FN_INTER,mul_assoc]
QED

Theorem rn_derivative_mul_rn_derivative:
    ∀sa mu nu lam dmdn dndl dmdl. measure_space (space sa,subsets sa,mu) ∧
        measure_space (space sa,subsets sa,nu) ∧ measure_space (space sa,subsets sa,lam) ∧
        dmdn ∈ rn_derivative sa mu nu ∧ dndl ∈ rn_derivative sa nu lam ∧
        (∀x. x ∈ space sa ⇒ dmdl x = dmdn x * dndl x) ⇒
        dmdl ∈ rn_derivative sa mu lam
Proof
    rw[] >> simp[rn_derivative_def,density_measure_def] >> irule_at Any IN_MEASURABLE_BOREL_MUL' >>
    qexistsl_tac [`dndl`,`dmdn`] >> simp[iffLR in_rn_derivative,le_mul,SF SFY_ss] >> rw[] >>
    `(λx. dmdn x * 𝟙 s x) ∈ Borel_measurable sa` by (
        irule IN_MEASURABLE_BOREL_MUL_INDICATOR >> simp[iffLR in_rn_derivative,SF SFY_ss]) >>
    `(∀x. x ∈ space sa ⇒ 0 ≤ (λx. dmdn x * 𝟙 s x) x)` by
        simp[iffLR in_rn_derivative,INDICATOR_FN_POS,le_mul,SF SFY_ss] >>
    dxrule_then (dxrule_then (qspecl_then [`nu`,`lam`,`dndl`] assume_tac)) rn_derivative_change_pos >>
    rfs[rn_derivative_def,density_measure_def] >> pop_assum kall_tac >> irule pos_fn_integral_cong >>
    simp[INDICATOR_FN_POS,le_mul] >> rw[indicator_fn_def] >> simp[mul_comm]
QED

Theorem rn_derivative_mul_AE_eq:
    ∀sa mu nu lam dmdl dmdn dndl. sigma_finite_measure_space (space sa,subsets sa,mu) ∧
        measure_space (space sa,subsets sa,nu) ∧ measure_space (space sa,subsets sa,lam) ∧
        dmdl ∈ rn_derivative sa mu lam ∧ dmdn ∈ rn_derivative sa mu nu ∧ dndl ∈ rn_derivative sa nu lam ⇒
        AE x::(space sa,subsets sa,lam). dmdl x = dmdn x * dndl x
Proof
    rw[] >>
    qspecl_then [`sa`,`mu`,`lam`,`dmdl`,`λx. dmdn x * dndl x`]
        (irule o SIMP_RULE (srw_ss ()) []) rn_derivative_unique >>
    simp[] >> qexists_tac `mu` >> simp[] >> irule rn_derivative_mul_rn_derivative >>
    fs[sigma_finite_measure_space_def] >> qexistsl_tac [`dmdn`,`dndl`,`nu`] >> simp[]
QED

Theorem rn_derivative_inv_AE_eq:
    ∀sa mu nu dmdn dndm. sigma_finite_measure_space (space sa,subsets sa,mu) ∧
        measure_space (space sa,subsets sa,nu) ∧
        dmdn ∈ rn_derivative sa mu nu ∧ dndm ∈ rn_derivative sa nu mu ⇒
        AE x::(space sa,subsets sa,mu). dndm x = (dmdn x)⁻¹
Proof
    rw[] >>
    qspecl_then [`(space sa,subsets sa,mu)`,`λx. dmdn x * dndm x = 1`,`λx. dndm x = (dmdn x)⁻¹`]
        (irule o SIMP_RULE (srw_ss ()) []) AE_subset >>
    CONJ_TAC >- simp[rinv_uniq] >>
    qspecl_then [`sa`,`mu`,`nu`,`mu`,`λx. 1`,`dmdn`,`dndm`]
        (irule o SIMP_RULE (srw_ss ()) []) rn_derivative_mul_AE_eq >>
    fs[sigma_finite_measure_space_def,rn_derivative_1] >> qexists_tac `nu` >> simp[]
QED

Theorem rn_derivative_density_measure:
    ∀m p q r f. measure_space m ∧ p ∈ Borel_measurable (sig_alg m) ∧ (∀x. x ∈ m_space m ⇒ 0 ≤ p x) ∧
        q ∈ Borel_measurable (sig_alg m) ∧ (∀x. x ∈ m_space m ⇒ 0 ≤ q x) ∧
        (AE x::m. q x ≠ +∞) ∧ (∀x. x ∈ m_space m ∧ q x = 0 ⇒ p x = 0) ∧
        (∀x. x ∈ m_space m ⇒ r x = p x * (q x)⁻¹) ⇒
        r ∈ rn_derivative (sig_alg m) (p * m) (q * m)
Proof
    rw[] >> simp[rn_derivative_def] >> CONJ_ASM1_TAC
    >- (irule IN_MEASURABLE_BOREL_MUL_INV >> simp[] >> qexistsl_tac [`p`,`q`] >> simp[]) >>
    CONJ_ASM1_TAC >> rw[]
    >- (Cases_on `q x = 0` >> simp[] >> irule le_mul >> simp[] >> irule le_inv >> simp[lt_le]) >>
    simp[GSYM density_def] >> simp[density_measure_def] >>
    resolve_then (Pos $ el 1) irule pos_fn_integral_density_clean EQ_TRANS >>
    irule_at Any pos_fn_integral_cong_AE >> simp[le_mul,INDICATOR_FN_POS] >>
    irule_at Any IN_MEASURABLE_BOREL_MUL' >> qexistsl_tac [`𝟙 s`,`r`] >> simp[] >>
    irule_at Any IN_MEASURABLE_BOREL_INDICATOR >> qexists_tac `s` >> simp[] >>
    qspecl_then [`m`,`λx. q x ≠ +∞`,`λx. q x * (r x * 𝟙 s x) = p x * 𝟙 s x`]
        (irule o SIMP_RULE (srw_ss ()) []) AE_subset >>
    rw[indicator_fn_def] >> Cases_on `q x = 0` >> simp[] >> simp[Once mul_comm,mul_assoc] >>
    `(q x)⁻¹ * q x = 1` suffices_by simp[] >> irule mul_linv >> simp[pos_not_neginf]
QED

Theorem rn_derivative_density_change_pos:
    ∀m p q f. measure_space m ∧ p ∈ Borel_measurable (sig_alg m) ∧ (∀x. x ∈ m_space m ⇒ 0 ≤ p x) ∧
        q ∈ Borel_measurable (sig_alg m) ∧ (∀x. x ∈ m_space m ⇒ 0 ≤ q x) ∧
        (AE x::m. q x ≠ +∞) ∧ (∀x. x ∈ m_space m ∧ q x = 0 ⇒ p x = 0) ∧
        f ∈ Borel_measurable (sig_alg m) ∧ (∀x. x ∈ m_space m ⇒ 0 ≤ f x) ⇒
        ∫⁺ (density m p) f = ∫⁺ (density m q) (λx. p x * (q x)⁻¹ * f x)
Proof
    rw[] >> qabbrev_tac `r = (λx. p x * (q x)⁻¹)` >> simp[] >>
    resolve_then Any (irule o SIMP_RULE (srw_ss ()) [GSYM density_def])
        rn_derivative_density_measure rn_derivative_change_pos >>
    simp[Abbr `r`] >> rw[] >> irule measure_space_density >> simp[]
QED

Theorem rn_derivative_density_change:
    ∀m p q f. measure_space m ∧ p ∈ Borel_measurable (sig_alg m) ∧ (∀x. x ∈ m_space m ⇒ 0 ≤ p x) ∧
        q ∈ Borel_measurable (sig_alg m) ∧ (∀x. x ∈ m_space m ⇒ 0 ≤ q x) ∧
        (AE x::m. q x ≠ +∞) ∧ (∀x. x ∈ m_space m ∧ q x = 0 ⇒ p x = 0) ∧ f ∈ Borel_measurable (sig_alg m) ⇒
        ∫ (density m p) f = ∫ (density m q) (λx. p x * (q x)⁻¹ * f x)
Proof
    rw[] >> qabbrev_tac `r = (λx. p x * (q x)⁻¹)` >> simp[] >>
    resolve_then Any (irule o SIMP_RULE (srw_ss ()) [GSYM density_def])
        rn_derivative_density_measure rn_derivative_change >>
    simp[Abbr `r`] >> rw[] >> irule measure_space_density >> simp[]
QED

(* better pos_simple_fn stuff *)

Definition psf_def:
    psf (s:num -> bool) e a x = ∑ (λi. Normal (a i) * 𝟙 (e i) x) s
End

Theorem psf_alt:
    ∀s e a. psf s e a = λx. ∑ (λi. Normal (a i) * 𝟙 (e i) x) s
Proof
    rw[FUN_EQ_THM,psf_def]
QED

Definition valid_psf_def:
    valid_psf sa s e (a:num -> real) ⇔
        FINITE s ∧ (∀i. i ∈ s ⇒ 0 ≤ a i) ∧ (∀i. i ∈ s ⇒ e i ∈ subsets sa)
End

Definition psf_integral_def:
    psf_integral mu s (e:num -> α -> bool) a = ∑ (λi. Normal (a i) * mu (e i)) s
End

Theorem pos_simple_fn_psf:
    (∀(m:α m_space) f s e a. pos_simple_fn m f s e a ⇒ valid_psf (sig_alg m) s e a) ∧
    (∀(sa: α algebra) mu f s e a.
        pos_simple_fn (space sa,subsets sa,mu) f s e a ⇒ valid_psf sa s e a)
Proof
    rw[pos_simple_fn_def,valid_psf_def]
QED

Theorem psf_pos_simple_fn:
    ∀sa s e a. algebra sa ∧ valid_psf sa s e a ⇒ ∃n ep ap. ∀mu.
        pos_simple_fn (space sa,subsets sa,mu) (psf s e a) (count n) ep ap ∧
        (measure_space (space sa,subsets sa,mu) ⇒
        psf_integral mu s e a = pos_simple_fn_integral (space sa,subsets sa,mu) (count n) ep ap)
Proof
    rpt strip_tac >> `FINITE s` by fs[valid_psf_def] >>
    qpat_x_assum `valid_psf _ _ _ _` mp_tac >> Induct_on `s` >> rw[]
    >- (qexistsl_tac [`1`,`λi. space sa`,`λi. 0`] >>
        rw[pos_simple_fn_def,psf_def,EXTREAL_SUM_IMAGE_EMPTY,
            EXTREAL_SUM_IMAGE_COUNT_ONE,ALGEBRA_SPACE,BIGUNION_IMAGE_COUNT_ONE,
            pos_simple_fn_integral_def,psf_integral_def,EXTREAL_SUM_IMAGE_EMPTY,
            normal_0,EXTREAL_SUM_IMAGE_COUNT_ONE]) >>
    rename [`k ∉ s`] >> `valid_psf sa s e a` by fs[valid_psf_def] >>
    fs[] >> pop_assum kall_tac >>
    qexistsl_tac [`2 * n`,
        `λi. if i < n then ep i ∩ ((space sa) DIFF e k) else ep (i - n) ∩ e k`,
        `λi. if i < n then ap i else ap (i - n) + a k`] >>
    strip_tac >> first_x_assum $ qspec_then `mu` assume_tac >>
    fs[pos_simple_fn_def,valid_psf_def,psf_def] >> rw[]
    >- (irule EXTREAL_SUM_IMAGE_POS >> rw[] >>
        irule le_mul >> simp[INDICATOR_FN_POS])
    >- (qmatch_abbrev_tac `_ f _ = _ g _` >>
        `∑ f (k INSERT s) = f k + ∑ f s` by (
            `∑ f (k INSERT s) = f k + ∑ f (s DELETE k)` suffices_by (rw[] >>
                NTAC 2 $ irule IRULER >> simp[GSYM DELETE_NON_ELEMENT]) >>
            irule EXTREAL_SUM_IMAGE_PROPERTY_NEG >> rw[] >> irule pos_not_neginf >>
            qunabbrev_tac `f` >> rw[] >> irule le_mul >> simp[INDICATOR_FN_POS]) >>
        fs[] >> pop_assum kall_tac >> qunabbrev_tac `f` >> fs[] >> qmatch_abbrev_tac `c + _ f _ = _` >>
        `∀i. i < n ⇒ f i ≠ −∞` by (rw[] >> irule pos_not_neginf >>
            qunabbrev_tac `f` >> rw[] >> irule le_mul >> simp[INDICATOR_FN_POS]) >>
        `∀i. i < 2 * n ⇒ g i ≠ −∞` by (rw[] >> irule pos_not_neginf >>
            qunabbrev_tac `g` >> rw[] >> irule le_mul >> simp[INDICATOR_FN_POS] >>
            irule REAL_LE_ADD >> simp[]) >>
        `∃i. i < n ∧ t ∈ ep i ∧ ∀j. j < n ∧ i ≠ j ⇒ t ∉ ep j` by (
            qpat_x_assum `BIGUNION _ = _` $
                (fn th => dxrule_then assume_tac $ iffRL $ SIMP_RULE bool_ss [EXTENSION] th) >>
            fs[IN_BIGUNION_IMAGE] >> rename [`i < n`] >> qexists_tac `i` >> rw[] >>
            first_x_assum $ dxrule_all_then assume_tac >> rfs[DISJOINT_ALT]) >>
        map_every (fn tms => qspecl_then tms assume_tac $
            SIMP_RULE bool_ss [GSYM RIGHT_FORALL_IMP_THM] EXTREAL_SUM_IMAGE_ZERO_DIFF)
            [[`count n`,`f`,`(count n) DIFF {i}`],
            [`count (2 * n)`,`g`,`(count (2 * n)) DIFF {i;i+n}`]] >>
        rfs[DIFF_DIFF_SUBSET] >>
        qspecl_then [`g`,`{i + n}`,`i`] assume_tac $
            SIMP_RULE bool_ss [GSYM RIGHT_FORALL_IMP_THM] EXTREAL_SUM_IMAGE_PROPERTY_NEG >>
        rfs[] >> `{i + n} DELETE i = {i + n}` by simp[GSYM DELETE_NON_ELEMENT] >>
        fs[EXTREAL_SUM_IMAGE_SING] >> NTAC 2 $ pop_assum kall_tac >>
        `(∀x. x < n ∧ x ≠ i ⇒ f x = 0)` by (rw[] >> qunabbrev_tac `f` >> simp[] >>
            DISJ2_TAC >> simp[indicator_fn_def]) >>
        `(∀x. x < 2 * n ∧ x ≠ i ∧ x ≠ i + n ⇒ g x = 0)` by (rw[] >> qunabbrev_tac `g` >>
            rw[] >> DISJ2_TAC >> simp[indicator_fn_def]) >>
        fs[] >> NTAC 5 $ pop_assum kall_tac >> NTAC 2 $ qpat_x_assum `∀i. _` kall_tac >>
        qunabbrevl_tac [`c`,`f`,`g`] >> simp[indicator_fn_def] >>
        Cases_on `t ∈ e k` >> simp[extreal_add_def])
    >- (irule ALGEBRA_INTER >> simp[] >> irule ALGEBRA_DIFF >> simp[ALGEBRA_SPACE])
    >- (irule ALGEBRA_INTER >> simp[])
    >- (irule REAL_LE_ADD >> simp[])
    >- (rename [`i ≠ j`] >> `DISJOINT (ep i) (ep j)` by fs[] >>
        pop_assum (fn th => rpt (pop_assum kall_tac) >> assume_tac th) >> fs[DISJOINT_ALT])
    >- (rpt (pop_assum kall_tac) >> rw[DISJOINT_ALT])
    >- (rpt (pop_assum kall_tac) >> rw[DISJOINT_ALT])
    >- (rename [`i ≠ j`] >> `DISJOINT (ep (i - n)) (ep (j - n))` by fs[] >>
        pop_assum (fn th => rpt (pop_assum kall_tac) >> assume_tac th) >> fs[DISJOINT_ALT])
    >- (qpat_x_assum `BIGUNION _ = _` $ assume_tac o GSYM >> simp[] >>
        rpt $ pop_assum kall_tac >> simp[EXTENSION,IN_BIGUNION_IMAGE] >> rw[] >> eq_tac >> rw[]
        >- (Cases_on `i < n` >> fs[] >> rw[]
            >- (qexists_tac `i` >> simp[])
            >- (qexists_tac `i - n` >> simp[]))
        >- (rename [`i < n`] >> Cases_on `x ∈ e k`
            >- (qexists_tac `i + n` >> simp[])
            >- (map_every (fn tm => qexists_tac tm >> simp[]) [`i`,`ep i`,`i`])))
    >- (fs[pos_simple_fn_integral_def,psf_integral_def] >>
        `(∀i. i = k ∨ i ∈ s ⇒ 0 ≤ mu (e i)) ∧ (∀i. i < n ⇒ 0 ≤ mu (ep i))` by (
            rw[] >> fs[measure_space_def,positive_def]) >>
        qmatch_abbrev_tac `_ f _ = _ g _` >>
        `∑ f (k INSERT s) = f k + ∑ f s` by (
            qpat_x_assum `∑ f s = _` kall_tac >>
            `∑ f (k INSERT s) = f k + ∑ f (s DELETE k)` suffices_by (rw[] >>
                NTAC 2 $ irule IRULER >> simp[GSYM DELETE_NON_ELEMENT]) >>
            irule EXTREAL_SUM_IMAGE_PROPERTY_NEG >> rw[] >> irule pos_not_neginf >>
            qunabbrev_tac `f` >> rw[] >> irule le_mul >> simp[]) >>
        fs[] >> pop_assum kall_tac >> qunabbrev_tac `f` >> fs[] >>
        qpat_x_assum `∑ _ _ = ∑ _ _` kall_tac >> qmatch_abbrev_tac `c + _ f _ = _` >>
        `(∀i. i < n ⇒ f i ≠ −∞) ∧ (∀i. i < 2 * n ⇒ g i ≠ −∞)` by (rw[] >>
            irule pos_not_neginf >> qunabbrevl_tac [`f`,`g`] >> rw[] >> irule le_mul >> simp[] >>
            TRY $ irule_at Any REAL_LE_ADD >> simp[] >> qmatch_abbrev_tac `_ ≤ _ eee` >>
            `eee ∈ subsets sa` suffices_by (rw[] >> fs[measure_space_def,positive_def]) >>
            qunabbrev_tac `eee` >> irule ALGEBRA_INTER >> simp[] >>
            irule ALGEBRA_COMPL >> simp[]) >>
        qspecl_then [`count n`,`(count (2 * n)) DIFF (count n)`,`g`] assume_tac $
            SIMP_RULE bool_ss [GSYM RIGHT_FORALL_IMP_THM] EXTREAL_SUM_IMAGE_DISJOINT_UNION >>
        qspecl_then [`count n`,`λi. i + n`,`g`] assume_tac $
            SIMP_RULE bool_ss [GSYM RIGHT_FORALL_IMP_THM] EXTREAL_SUM_IMAGE_IMAGE >>
        rfs[INJ_DEF,DISJOINT_ALT] >>
        `count n ∪ (count (2 * n) DIFF count n) = count (2 * n)` by (
            irule $ cj 1 UNION_DIFF >> simp[SUBSET_DEF]) >>
        `IMAGE (λi. i + n) (count n) = count (2 * n) DIFF count n` by (
            rw[EXTENSION] >> eq_tac >> rw[] >> qexists_tac `x - n` >> simp[]) >>
        fs[o_DEF] >> NTAC 4 $ pop_assum kall_tac >> simp[GSYM EXTREAL_SUM_IMAGE_ADD] >>
        `(∀i. i < n ⇒ mu (ep i ∩ e k) ≠ −∞) ∧ (∀i. i < n ⇒ mu (ep i ∩ (space sa DIFF e k)) ≠ −∞)` by (
            rw[] >> irule pos_not_neginf >> qmatch_abbrev_tac `_ ≤ _ eee` >>
            `eee ∈ subsets sa` suffices_by (rw[] >> fs[measure_space_def,positive_def]) >>
            qunabbrev_tac `eee` >> irule ALGEBRA_INTER >> simp[] >>
            irule ALGEBRA_COMPL >> simp[]) >>
        `∑ (λi. g i + g (i + n)) (count n) = ∑ (λi. f i + Normal (a k) * mu (ep i ∩ e k)) (count n)` by (
            irule EXTREAL_SUM_IMAGE_EQ >> simp[] >> REVERSE CONJ_ASM1_TAC
            >- (pop_assum $ assume_tac o GSYM >> simp[] >> DISJ1_TAC >> rw[] >>
                irule $ cj 1 add_not_infty >> simp[]) >>
            rw[FUN_EQ_THM] >> rename [`i < n`] >> qunabbrevl_tac [`f`,`g`] >>
            simp[GSYM extreal_add_def] >> simp[add_rdistrib] >>
            simp[mul_not_infty,add_assoc] >>
            qunabbrev_tac `c` >> qmatch_abbrev_tac `c * s1 + c * s2 + z = c * s3 + z` >>
            `0 ≤ s1 ∧ 0 ≤ s2 ∧ s1 + s2 = s3` suffices_by (rw[] >> simp[GSYM add_ldistrib]) >>
            qunabbrevl_tac [`c`,`s1`,`s2`,`s3`,`z`] >> drule_then assume_tac MEASURE_SPACE_POSITIVE >>
            fs[positive_def] >> pop_assum (fn th => NTAC 2 $ irule_at Any th) >> pop_assum kall_tac >>
            qspecl_then [`(space sa,subsets sa,mu)`,`ep i ∩ (space sa DIFF e k)`,`ep i ∩ e k`]
                assume_tac (GSYM MEASURE_ADDITIVE) >> rfs[DISJOINT_ALT] >>
            `ep i ∩ (space sa DIFF e k) ∪ ep i ∩ e k = ep i` by (
                rw[EXTENSION] >> eq_tac >> rw[] >> `ep i ∈ subsets sa` by simp[] >>
                fs[algebra_def,subset_class_def] >> last_x_assum $ dxrule_then assume_tac >>
                rfs[SUBSET_DEF]) >>
            fs[] >> pop_assum kall_tac >> pop_assum $ irule_at Any >>
            NTAC 2 $ irule_at Any ALGEBRA_INTER >> simp[] >> irule ALGEBRA_COMPL >> simp[]) >>
        fs[] >> pop_assum kall_tac >>
        qspecl_then [`count n`,`f`,`λi. Normal (a k) * mu (ep i ∩ e k)`] assume_tac $
            SIMP_RULE bool_ss [GSYM RIGHT_FORALL_IMP_THM] EXTREAL_SUM_IMAGE_ADD >>
        qspecl_then [`count n`,`λi. mu (ep i ∩ e k)`,`a k`] assume_tac $
            SIMP_RULE bool_ss [GSYM RIGHT_FORALL_IMP_THM] EXTREAL_SUM_IMAGE_CMUL >>
        rfs[mul_not_infty] >> NTAC 2 $ pop_assum kall_tac >>
        `∑ (λi. mu (ep i ∩ e k)) (count n) = mu (e k)` by (
            qspecl_then [`(space sa,subsets sa,mu)`,`e k`,`λi. ep i ∩ e k`,`n`] assume_tac FINITE_ADDITIVE >>
            rfs[MEASURE_FINITE_ADDITIVE,DISJOINT_ALT,o_DEF] >> pop_assum irule >> rw[]
            >- (last_x_assum irule >> simp[] >> qexists_tac `i` >> simp[])
            >- (irule ALGEBRA_INTER >> simp[]) >>
            rw[EXTENSION,IN_BIGUNION_IMAGE] >> eq_tac >> rw[] >>
            `e k ∈ subsets sa` by simp[] >> `e k ⊆ space sa` by fs[algebra_def,subset_class_def] >>
            fs[SUBSET_DEF] >> pop_assum $ dxrule_then assume_tac >> fs[EXTENSION,IN_BIGUNION_IMAGE]) >>
        fs[] >> pop_assum kall_tac >> irule add_comm >> DISJ1_TAC >>
        irule_at Any $ cj 1 EXTREAL_SUM_IMAGE_NOT_INFTY >> fs[] >>
        qunabbrev_tac `c` >> irule pos_not_neginf >> irule le_mul >> simp[])
QED

Theorem psf_pos_simple_fn_spec:
    ∀m s e a. measure_space m ∧ valid_psf (sig_alg m) s e a ⇒
        ∃sp ep ap. pos_simple_fn m (psf s e a) sp ep ap ∧
        psf_integral (measure m) s e a = pos_simple_fn_integral m sp ep ap
Proof
    rw[] >> drule_at_then Any assume_tac psf_pos_simple_fn >>
    rfs[SIMP_RULE bool_ss [re_sig_alg] (iffLR measure_space_def),iffLR sigma_algebra_def] >>
    pop_assum $ qspec_then `measure m` assume_tac >> rfs[] >>
    qexistsl_tac [`count n`,`ep`,`ap`] >> simp[]
QED

Theorem pos_fn_integral_alt:
    ∀m f. measure_space m ⇒ ∫⁺ m f = sup {psf_integral mu s e a | mu = measure m ∧
        valid_psf (sig_alg m) s e a ∧ ∀x. x ∈ m_space m ⇒ psf s e a x ≤ f x}
Proof
    rw[pos_fn_integral_def] >> irule IRULER >> rw[EXTENSION] >> eq_tac >> rw[]
    >- (fs[psfis_def,psfs_def] >> rw[] >> rename [`pos_simple_fn m g s e a`] >>
        qexistsl_tac [`s`,`e`,`a`] >> simp[pos_simple_fn_integral_def,psf_integral_def] >>
        rfs[pos_simple_fn_def,valid_psf_def,psf_def])
    >- (qexists_tac `psf s e a` >> simp[] >> fs[psfis_def,psfs_def] >>
        dxrule_all_then assume_tac psf_pos_simple_fn_spec >> fs[] >>
        qexists_tac `sp,ep,ap` >> simp[])
QED

Theorem IN_MEASURABLE_BOREL_PSF:
    ∀sa s e a. sigma_algebra sa ∧ valid_psf sa s e a ⇒ psf s e a ∈ Borel_measurable sa
Proof
    rw[valid_psf_def,psf_alt] >>
    irule $ INST_TYPE [beta |-> ``:num``] IN_MEASURABLE_BOREL_SUM >> simp[] >>
    qexistsl_tac [`λi x. Normal (a i) * 𝟙 (e i) x`,`s`] >> rw[]
    >- (irule pos_not_neginf >> irule le_mul >> simp[INDICATOR_FN_POS]) >>
    irule IN_MEASURABLE_BOREL_CMUL >> simp[] >>
    qexistsl_tac [`𝟙 (e i)`,`a i`] >> simp[] >>
    irule IN_MEASURABLE_BOREL_INDICATOR >> simp[] >> qexists_tac `e i` >> simp[]
QED

Theorem valid_psf_empty:
    ∀sa a e. valid_psf sa ∅ a e
Proof
    rw[valid_psf_def]
QED

Theorem psf_empty:
    ∀a e x. psf ∅ a e x = 0
Proof
    rw[psf_def,EXTREAL_SUM_IMAGE_EMPTY]
QED

Theorem psf_integral_empty:
    ∀mu a e. psf_integral mu ∅ a e = 0
Proof
    rw[psf_integral_def,EXTREAL_SUM_IMAGE_EMPTY]
QED

Theorem pos_fn_integral_psf:
    ∀m s e a. measure_space m ∧ valid_psf (sig_alg m) s e a ⇒
        ∫⁺ m (psf s e a) = psf_integral (measure m) s e a
Proof
    rw[] >> drule_all_then assume_tac psf_pos_simple_fn_spec >> rfs[] >>
    irule pos_fn_integral_pos_simple_fn >> simp[]
QED

Theorem psf_pos:
    ∀sa s e a x. valid_psf sa s e a ∧ x ∈ space sa ⇒ 0 ≤ psf s e a x
Proof
    rw[valid_psf_def,psf_def] >> irule EXTREAL_SUM_IMAGE_POS >> rw[] >>
    irule le_mul >> simp[INDICATOR_FN_POS]
QED

Theorem integral_psf:
    ∀m s e a. measure_space m ∧ valid_psf (sig_alg m) s e a ⇒
        ∫ m (psf s e a) = psf_integral (measure m) s e a
Proof
    rw[GSYM pos_fn_integral_psf] >> irule integral_pos_fn >> rw[] >>
    irule psf_pos >> qexists_tac `sig_alg m` >> simp[]
QED

Theorem pfs_max:
    ∀sa fs fe fa gs ge ga. sigma_algebra sa ∧ valid_psf sa fs fe fa ∧ valid_psf sa gs ge ga ⇒
        ∃hs he ha. valid_psf sa hs he ha ∧
        ∀x. x ∈ space sa ⇒ psf hs he ha x = max (psf fs fe fa x) (psf gs ge ga x)
Proof
    rw[] >> dxrule_then assume_tac measure_space_trivial >>
    dxrule_then assume_tac $ cj 1 $ iffLR sigma_finite_measure_space_def >>
    drule_then assume_tac psf_pos_simple_fn_spec >> rfs[] >>
    pop_assum imp_res_tac >> fs[] >>
    dxrule_all_then assume_tac pos_simple_fn_max >> fs[] >>
    rename [`pos_simple_fn _ _ s e a`] >> qexistsl_tac [`s`,`e`,`a`] >>
    drule_then assume_tac $ cj 2 pos_simple_fn_psf >> rw[] >>
    fs[pos_simple_fn_def,psf_def]
QED

Theorem psf_integral_pos:
    ∀m s e a. measure_space m ∧ valid_psf (sig_alg m) s e a ⇒
        0 ≤ psf_integral (measure m) s e a
Proof
    rw[valid_psf_def,psf_integral_def] >> irule EXTREAL_SUM_IMAGE_POS >> rw[] >>
    irule le_mul >> fs[measure_space_def,positive_def]
QED

Theorem psf_integral_mono:
    ∀m s e a t f b. measure_space m ∧ valid_psf (sig_alg m) s e a ∧ valid_psf (sig_alg m) t f b ∧
        (∀x. x ∈ m_space m ⇒ psf s e a x ≤ psf t f b x) ⇒
        psf_integral (measure m) s e a ≤ psf_integral (measure m) t f b
Proof
    rw[] >> drule_then assume_tac psf_pos_simple_fn_spec >> rfs[] >>
    pop_assum (fn th => NTAC 2 $ dxrule_then assume_tac th) >> fs[] >>
    drule_all_then assume_tac pos_simple_fn_integral_mono >> simp[]
QED

(* pos_fn_seq stuff *)

Definition valid_psf_seq_def:
    valid_psf_seq sa si ei ai ⇔
        (∀i. valid_psf sa (si i) (ei i) (ai i)) ∧
        (∀x. x ∈ space sa ⇒ mono_increasing (λi. psf (si i) (ei i) (ai i) x))
End

Definition psf_seq_lim_def:
    psf_seq_lim si ei ai x = sup (IMAGE (λi. psf (si i) (ei i) (ai i) x) 𝕌(:num))
End

Theorem pos_fn_sup_psf_seq:
    ∀sa f. sigma_algebra sa ∧ f ∈ Borel_measurable sa ∧
        (∀x. x ∈ space sa ⇒ 0 ≤ f x) ⇒
        ∃si ei ai. valid_psf_seq sa si ei ai ∧
        ∀x. x ∈ space sa ⇒ f x = psf_seq_lim si ei ai x
Proof
    rw[] >>
    qspecl_then [`(space sa,subsets sa,λx.0)`,`f`] assume_tac $ cj 1 measurable_sequence >>
    rfs[measure_space_trivial,iffLR sigma_finite_measure_space_def] >>
    `∃si ei ai. ∀i. pos_simple_fn (space sa,subsets sa,(λx. 0)) (fi i) (si i) (ei i) (ai i)` by (
        simp[GSYM SKOLEM_THM] >> strip_tac >>
        qpat_x_assum `∀i. _ ∈ psfis _ _` $ qspec_then `i` assume_tac >> fs[psfis_def,psfs_def] >>
        rename [`pos_simple_fn _ _ s e a`] >> qexistsl_tac [`s`,`e`,`a`] >> simp[]) >>
    qexistsl_tac [`si`,`ei`,`ai`] >>
    fs[pos_simple_fn_def,valid_psf_seq_def,valid_psf_def,psf_def,psf_seq_lim_def] >>
    rw[] >> fs[ext_mono_increasing_def] >> rw[] >> rename [`_ _ (si i) ≤ _ _ (si j)`] >>
    first_x_assum $ qspecl_then [`x`,`i`,`j`] assume_tac >> rfs[]
QED

Theorem pos_fn_psf_integral_convergence:
    ∀m f si ei ai. measure_space m ∧ valid_psf_seq (sig_alg m) si ei ai ∧
        (∀x. x ∈ m_space m ⇒ f x = psf_seq_lim si ei ai x) ⇒
        ∫⁺ m f = sup (IMAGE (λi. psf_integral (measure m) (si i) (ei i) (ai i)) 𝕌(:num))
Proof
    rw[valid_psf_seq_def] >>
    `(λi. psf_integral (measure m) (si i) (ei i) (ai i)) =
        (λi. ∫⁺ m ((λi. psf (si i) (ei i) (ai i)) i))` by (
        rw[FUN_EQ_THM] >> simp[GSYM pos_fn_integral_psf]) >>
    PURE_ASM_REWRITE_TAC [] >> pop_assum kall_tac >> irule lebesgue_monotone_convergence >> rw[]
    >- (simp[psf_def,psf_seq_lim_def])
    >- (irule psf_pos >> qexists_tac `sig_alg m` >> simp[])
    >- (irule IN_MEASURABLE_BOREL_PSF >> simp[MEASURE_SPACE_SIGMA_ALGEBRA])
QED

(* Measure ops *)

Theorem psf_integral_measure_add:
    ∀sa mu nu mnu s e a. measure_space (space sa,subsets sa,mu) ∧ measure_space (space sa,subsets sa,nu) ∧
        valid_psf sa s e a ∧ (∀s. s ∈ subsets sa ⇒ mnu s = mu s + nu s) ⇒
        psf_integral mnu s e a = psf_integral mu s e a + psf_integral nu s e a
Proof
    rw[measure_space_def,positive_def,valid_psf_def,psf_integral_def] >>
    qspecl_then [`s`,`(λi. Normal (a i) * mu (e i))`,`(λi. Normal (a i) * nu (e i))`] assume_tac $
        SIMP_RULE pure_ss [GSYM RIGHT_FORALL_IMP_THM] EXTREAL_SUM_IMAGE_ADD >> rfs[] >>
    `∑ (λi. Normal (a i) * mnu (e i)) s = ∑ (λx. Normal (a x) * mu (e x) + Normal (a x) * nu (e x)) s` by (
        irule EXTREAL_SUM_IMAGE_EQ >> simp[] >> CONJ_ASM1_TAC >> rw[] >- (irule add_ldistrib >> simp[]) >>
        DISJ1_TAC >> rw[] >> irule pos_not_neginf >> irule le_add >> rw[] >>
        irule le_mul >> simp[]) >>
    fs[] >> pop_assum kall_tac >> pop_assum irule >> DISJ1_TAC >>
    rw[] >> irule pos_not_neginf >> irule le_mul >> simp[]
QED

Theorem psf_integral_measure_sum:
    ∀sa mui nu t s e a. FINITE t ∧ sigma_algebra sa ∧ valid_psf sa s e a ∧
        (∀i. i ∈ t ⇒ measure_space (space sa,subsets sa,mui i)) ∧
        (∀r. r ∈ subsets sa ⇒ nu r = ∑ (C mui r) t) ⇒
        psf_integral nu s e a = ∑ (λi. psf_integral (mui i) s e a) t
Proof
    `∀(t:β->bool). FINITE t ⇒ ∀(sa:α algebra) mui nu s e a. sigma_algebra sa ∧ valid_psf sa s e a ∧
        (∀i. i ∈ t ⇒ measure_space (space sa,subsets sa,mui i)) ∧
        (∀r. r ∈ subsets sa ⇒ nu r = ∑ (C mui r) t) ⇒
        psf_integral nu s e a = ∑ (λi. psf_integral (mui i) s e a) t` suffices_by (rw[] >>
        last_x_assum $ drule_then assume_tac >> pop_assum $ drule_all_then assume_tac >> simp[]) >>
    Induct_on `t` >> rw[]
    >- (fs[EXTREAL_SUM_IMAGE_EMPTY,psf_integral_def] >>
        irule EXTREAL_SUM_IMAGE_0 >> gs[valid_psf_def]) >>
    rename [`n ∉ t`,`valid_psf sa s e a`] >>
    `∑ (λi. psf_integral (mui i) s e a) (n INSERT t) =
        psf_integral (mui n) s e a + ∑ (λi. psf_integral (mui i) s e a) t` by (
        qspecl_then [`(λi. psf_integral (mui i) s e a)`,`t`,`n`]
            (fn th => assume_tac th >> rfs[DELETE_NON_ELEMENT_RWT] >> pop_assum irule) $
            SIMP_RULE bool_ss [GSYM RIGHT_FORALL_IMP_THM] EXTREAL_SUM_IMAGE_PROPERTY >>
        DISJ1_TAC >> rw[] >> irule pos_not_neginf >>
        qspec_then `space sa,subsets sa,mu`
            (irule o SIMP_RULE (srw_ss ()) [] o GEN ``mu:α measure``) psf_integral_pos >>
        qexists_tac `sa` >> simp[]) >>
    pop_assum SUBST1_TAC >>
    last_x_assum $ qspecl_then [`sa`,`mui`,`λr. ∑ (C mui r) t`,`s`,`e`,`a`] assume_tac >>
    rfs[] >> pop_assum $ SUBST1_TAC o SYM >> irule psf_integral_measure_add >>
    qexists_tac `sa` >> simp[] >>
    qspecl_then [`sa`,`mui`,`λr. ∑ (C mui r) t`,`t`] assume_tac measure_space_sum >> rfs[] >>
    qx_gen_tac `r` >> DISCH_TAC >>
    qspecl_then [`C mui r`,`t`,`n`]
        (fn th => assume_tac th >> rfs[DELETE_NON_ELEMENT_RWT] >> pop_assum irule) $
        SIMP_RULE bool_ss [GSYM RIGHT_FORALL_IMP_THM] EXTREAL_SUM_IMAGE_PROPERTY >>
    DISJ1_TAC >> rw[] >> irule pos_not_neginf >> fs[measure_space_def,positive_def]
QED

Theorem psf_integral_measure_cmul:
    ∀sa mu nu s e a c. measure_space (space sa,subsets sa,mu) ∧
        valid_psf sa s e a ∧ (∀s. s ∈ subsets sa ⇒ nu s = Normal c * mu s) ⇒
        psf_integral nu s e a = Normal c * psf_integral mu s e a
Proof
    rw[measure_space_def,positive_def,valid_psf_def,psf_integral_def] >>
    qspecl_then [`s`,`(λi. Normal (a i) * mu (e i))`,`c`] assume_tac $
        SIMP_RULE pure_ss [GSYM RIGHT_FORALL_IMP_THM] EXTREAL_SUM_IMAGE_CMUL >> rfs[] >>
    `∑ (λi. Normal (a i) * nu (e i)) s = ∑ (λx. Normal c * (Normal (a x) * mu (e x))) s` by (
        irule EXTREAL_SUM_IMAGE_EQ >> simp[] >> CONJ_ASM1_TAC >> rw[]
        >- (simp[mul_assoc,extreal_mul_def]) >> `0 ≤ c ∨ c ≤ 0` by simp[]
        >| [DISJ1_TAC,DISJ2_TAC] >> rw[]
        >| [irule $ cj 1 mul_not_infty,irule $ cj 3 mul_not_infty] >> simp[] >>
        irule pos_not_neginf >> irule le_mul >> simp[]) >>
    fs[] >> pop_assum kall_tac >> pop_assum irule >> DISJ1_TAC >>
    rw[] >> irule pos_not_neginf >> irule le_mul >> simp[]
QED

Theorem psf_integral_measure_suminf:
    ∀sa mun nu s e a. (∀n. measure_space (space sa,subsets sa,mun n)) ∧ valid_psf sa s e a ∧
        (∀t. t ∈ subsets sa ⇒ nu t = suminf (C mun t)) ⇒
        psf_integral nu s e a = suminf (λn. psf_integral (mun n) s e a)
Proof
    rw[psf_integral_def] >> rfs[valid_psf_def] >>
    `∀i n. i ∈ s ⇒ 0 ≤ mun n (e i)` by (rw[] >> fs[measure_space_def,positive_def]) >>
    qspecl_then [`λ i n. Normal (a i) * mun n (e i)`,`s`] assume_tac ext_suminf_sigma_gen >>
    `∀i j. i ∈ s ⇒ 0 ≤ Normal (a i) * mun j (e i)` by (rw[] >> irule le_mul >> gs[]) >>
    gs[] >> pop_assum kall_tac >> pop_assum $ SUBST1_TAC o SYM >>
    irule EXTREAL_SUM_IMAGE_EQ >> simp[] >> REVERSE CONJ_ASM1_TAC
    >- (simp[] >> DISJ1_TAC >> rw[] >> irule pos_not_neginf >> irule ext_suminf_pos >>
        rw[] >> irule le_mul >> simp[]) >> rw[] >>
    qspecl_then [`C mun (e x)`,`Normal (a x)`]
        (irule o SIMP_RULE (srw_ss ()) [] o GSYM) ext_suminf_cmul >> simp[]
QED

Theorem pos_simple_fn_psf:
    (∀(m:α m_space) f s e a. pos_simple_fn m f s e a ⇒ valid_psf (sig_alg m) s e a) ∧
    (∀(sa: α algebra) mu f s e a.
        pos_simple_fn (space sa,subsets sa,mu) f s e a ⇒ valid_psf sa s e a)
Proof
    rw[pos_simple_fn_def,valid_psf_def]
QED

Theorem pfs_max:
    ∀sa fs fe fa gs ge ga. sigma_algebra sa ∧ valid_psf sa fs fe fa ∧ valid_psf sa gs ge ga ⇒
        ∃hs he ha. valid_psf sa hs he ha ∧
        ∀x. x ∈ space sa ⇒ psf hs he ha x = max (psf fs fe fa x) (psf gs ge ga x)
Proof
    rw[] >> dxrule_then assume_tac measure_space_trivial >>
    dxrule_then assume_tac $ cj 1 $ iffLR sigma_finite_measure_space_def >>
    drule_then assume_tac psf_pos_simple_fn_spec >> rfs[] >>
    pop_assum imp_res_tac >> fs[] >>
    dxrule_all_then assume_tac pos_simple_fn_max >> fs[] >>
    rename [`pos_simple_fn _ _ s e a`] >> qexistsl_tac [`s`,`e`,`a`] >>
    drule_then assume_tac $ cj 2 pos_simple_fn_psf >> rw[] >>
    fs[pos_simple_fn_def,psf_def]
QED

Theorem psf_integral_mono:
    ∀m s e a t f b. measure_space m ∧ valid_psf (sig_alg m) s e a ∧ valid_psf (sig_alg m) t f b ∧
        (∀x. x ∈ m_space m ⇒ psf s e a x ≤ psf t f b x) ⇒
        psf_integral (measure m) s e a ≤ psf_integral (measure m) t f b
Proof
    rw[] >> drule_then assume_tac psf_pos_simple_fn_spec >> rfs[] >>
    pop_assum (fn th => NTAC 2 $ dxrule_then assume_tac th) >> fs[] >>
    drule_all_then assume_tac pos_simple_fn_integral_mono >> simp[]
QED

Theorem pos_fn_integral_const:
    ∀m c. measure_space m ∧ 0 ≤ c ⇒ ∫⁺ m (λx. c) = c * measure m (m_space m)
Proof
    rw[] >> qspecl_then [`𝟙 (m_space m)`,`c`,`m`] assume_tac pos_fn_integral_cmult >> rfs[] >>
    drule_then assume_tac MEASURE_SPACE_MSPACE_MEASURABLE >>
    `𝟙 (m_space m) ∈ Borel_measurable (sig_alg m)` by (irule IN_MEASURABLE_BOREL_INDICATOR >>
        fs[measure_space_def] >> qexists_tac `m_space m` >> simp[]) >>
    `(𝟙 (m_space m))⁺ = 𝟙 (m_space m)` by (rw[FUN_EQ_THM,fn_plus_def,indicator_fn_def] >>
        Cases_on `x ∈ m_space m` >> simp[]) >>
    gs[pos_fn_integral_indicator] >> NTAC 3 $ pop_assum kall_tac >> pop_assum $ SUBST1_TAC o SYM >>
    irule pos_fn_integral_cong >> simp[indicator_fn_def]
QED

Theorem pos_fn_integral_zero_measure:
    ∀sa f. sigma_algebra sa ∧ (∀x. x ∈ space sa ⇒ 0 ≤ f x) ⇒
        ∫⁺ (space sa,subsets sa,(λs. 0)) f = 0
Proof
    rw[] >> irule $ iffLR le_antisym >> rw[]
    >- (`∀x1 x2 x3. x1 ≤ x2 ∧ x2 = x3 ⇒ x1 ≤ x3` by simp[] >> pop_assum irule >>
        qexists_tac `∫⁺ (space sa,subsets sa,(λs. 0)) (λx. +∞ * 𝟙 (space sa) x)` >>
        irule_at Any pos_fn_integral_mono >> rw[] >- rw[indicator_fn_def] >>
        dxrule_then assume_tac measure_space_trivial >> fs[sigma_finite_measure_space_def] >>
        map_every (drule_then assume_tac)
            [MEASURE_SPACE_MSPACE_MEASURABLE,pos_fn_integral_cmul_indicator'] >> rfs[])
    >- (irule pos_fn_integral_pos >> simp[] >>
        dxrule_then assume_tac measure_space_trivial >> fs[sigma_finite_measure_space_def])
QED

Theorem pos_fn_integral_fixed_state_measure:
    ∀sa x f. sigma_algebra sa ∧ x ∈ space sa ∧
        (∀x. x ∈ space sa ⇒ 0 ≤ f x) ∧ f ∈ Borel_measurable sa ⇒
        ∫⁺ (space sa,subsets sa,C 𝟙 x) f = f x
Proof
    rw[] >> drule_then (qspec_then `x` assume_tac) measure_space_fixed_state_measure >>
    qmatch_abbrev_tac `∫⁺ m f = _` >> irule $ iffLR le_antisym >> rw[]
    >- (qspecl_then [`m`,`f`,`{y | f y ≤ f x} ∩ space sa`] assume_tac pos_fn_integral_split >>
        rfs[Abbr `m`,IN_MEASURABLE_BOREL_ALL] >> pop_assum kall_tac >>
        qmatch_abbrev_tac `∫⁺ m (λy. f y * 𝟙 s y) + _ ≤ _` >>
        `∀x1 x2 x3. x1 ≤ x2 ∧ x2 = x3 ⇒ x1 ≤ x3` by simp[] >> pop_assum irule >>
        qexists_tac `∫⁺ m (λy. f x * 𝟙 s y) + ∫⁺ m (λy. +∞ * 𝟙 (space sa DIFF s) y)` >>
        irule_at Any le_add2 >> NTAC 2 $ irule_at Any pos_fn_integral_mono >>
        simp[Abbr `s`,Abbr `m`,IN_MEASURABLE_BOREL_ALL,SIGMA_ALGEBRA_COMPL,pos_fn_integral_cmul_indicator'] >>
        rw[indicator_fn_def])
    >- (qspecl_then [`m`,`f`,`{y | f x ≤ f y} ∩ space sa`] assume_tac pos_fn_integral_split >>
        rfs[Abbr `m`,IN_MEASURABLE_BOREL_ALL] >> pop_assum kall_tac >>
        qmatch_abbrev_tac `_ ≤ ∫⁺ m (λy. f y * 𝟙 s y) + _` >>
        `∀x1 x2 x3. x1 = x2 ∧ x2 ≤ x3 ⇒ x1 ≤ x3` by simp[] >> pop_assum irule >>
        qexists_tac `∫⁺ m (λy. f x * 𝟙 s y) + ∫⁺ m (λy. 0 * 𝟙 (space sa DIFF s) y)` >>
        irule_at Any le_add2 >> NTAC 2 $ irule_at Any pos_fn_integral_mono >>
        simp[Abbr `s`,Abbr `m`,IN_MEASURABLE_BOREL_ALL,SIGMA_ALGEBRA_COMPL,
            pos_fn_integral_cmul_indicator',pos_fn_integral_zero] >>
        rw[indicator_fn_def])
QED

Theorem pos_fn_integral_measure_add:
    ∀sa mu nu mnu f. measure_space (space sa,subsets sa,mu) ∧ measure_space (space sa,subsets sa,nu) ∧
        (∀x. x ∈ space sa ⇒ 0 ≤ f x) ∧ (∀s. s ∈ subsets sa ⇒ mnu s = mu s + nu s) ⇒
        ∫⁺ (space sa,subsets sa,mnu) f = ∫⁺ (space sa,subsets sa,mu) f + ∫⁺ (space sa,subsets sa,nu) f
Proof
    rw[] >> drule_all_then assume_tac measure_space_add >> simp[pos_fn_integral_alt] >>
    qmatch_abbrev_tac `_ = sup p + sup q` >>
    `sup p ≠ −∞ ∧ sup q ≠ −∞` by (rw[] >> irule pos_not_neginf >>
        irule le_sup_imp >> qunabbrevl_tac [`p`,`q`] >> simp[]
        >| [qexists_tac `mu,∅,(λi.∅),(λi.0)`,qexists_tac `nu,∅,(λi.∅),(λi.0)`] >> simp[] >>
        rw[psf_integral_def,valid_psf_def,psf_def,EXTREAL_SUM_IMAGE_EMPTY]) >>
    simp[sup_add] >> NTAC 2 $ pop_assum kall_tac >> qunabbrevl_tac [`p`,`q`] >>
    irule $ iffLR le_antisym >> CONJ_TAC >> irule sup_le_sup_imp >> rw[]
    >- (rename [`(_,_) = _ msea`] >>
        `∃mnu' s e a. msea = (mnu',s,e,a)` by metis_tac[ABS_PAIR_THM] >> fs[] >> rw[] >>
        qexists_tac `psf_integral mnu s e a` >> simp[] >>
        qexists_tac `(psf_integral mu s e a,psf_integral nu s e a)` >> simp[] >>
        irule_at Any psf_integral_measure_add >> qexistsl_tac [`nu,s,e,a`,`mu,s,e,a`,`sa`] >> simp[])
    >- (rename [`(z,T) = _ xy`] >> Cases_on `xy` >> fs[] >>
        rename [`z = x + y`,`(x,T) = _ x4`,`(y,T) = _ y4`] >>
        `∃mu' fs fe fa. x4 = (mu',fs,fe,fa)` by metis_tac[ABS_PAIR_THM] >>
        `∃nu' gs ge ga. y4 = (nu',gs,ge,ga)` by metis_tac[ABS_PAIR_THM] >> fs[] >> rw[] >>
        drule_then assume_tac $ cj 2 MEASURE_SPACE_SIGMA_ALGEBRA >>
        qspecl_then [`sa`,`fs`,`fe`,`fa`,`gs`,`ge`,`ga`] assume_tac pfs_max >> rfs[] >>
        qexists_tac `psf_integral mnu hs he ha` >>
        drule_all_then assume_tac psf_integral_measure_add >> fs[] >>
        irule_at Any le_add2 >> qexists_tac `mnu,hs,he,ha` >> simp[] >> pop_assum kall_tac >>
        qspec_then `(space sa,subsets sa,meas)`
            (assume_tac o SIMP_RULE (srw_ss ()) [] o Q.GEN `meas`)
            psf_integral_mono >> pop_assum (NTAC 2 o irule_at Any) >>
        simp[le_max,max_le])
QED

Theorem pos_fn_integral_measure_sum:
    ∀sa mui nu s f. FINITE s ∧ sigma_algebra sa ∧
       (∀i. i ∈ s ⇒ measure_space (space sa,subsets sa,mui i)) ∧
       (∀x. x ∈ space sa ⇒ 0 ≤ f x) ∧ (∀t. t ∈ subsets sa ⇒ nu t = ∑ (C mui t) s) ⇒
       ∫⁺ (space sa,subsets sa,nu) f = ∑ (λi. ∫⁺ (space sa,subsets sa,mui i) f) s
Proof
    `∀(s:β->bool). FINITE s ⇒ ∀(sa:α algebra) mui nu f. sigma_algebra sa ∧
       (∀i. i ∈ s ⇒ measure_space (space sa,subsets sa,mui i)) ∧
       (∀x. x ∈ space sa ⇒ 0 ≤ f x) ∧ (∀t. t ∈ subsets sa ⇒ nu t = ∑ (C mui t) s) ⇒
       ∫⁺ (space sa,subsets sa,nu) f = ∑ (λi. ∫⁺ (space sa,subsets sa,mui i) f) s` suffices_by (rw[] >>
       last_x_assum $ drule_then assume_tac >> pop_assum $ drule_all_then assume_tac >> simp[]) >>
    Induct_on `s` >> rw[]
    >- (fs[EXTREAL_SUM_IMAGE_EMPTY] >>
        `measure_space (space sa,subsets sa,nu)` by (irule measure_space_cong >>
            qexists_tac `λx. 0` >> simp[] >> drule_then assume_tac measure_space_trivial >>
            fs[sigma_finite_measure_space_def]) >>
        simp[pos_fn_integral_alt] >> qmatch_abbrev_tac `_ p = _` >>
        `p = {0}` suffices_by rw[sup_sing] >> rw[FUN_EQ_THM,Abbr `p`] >> eq_tac >> rw[]
        >- (rename [`(_,T) = _ msea`] >> `∃mu s e a. msea = (mu,s,e,a)` by metis_tac[ABS_PAIR_THM] >>
            rw[] >> fs[valid_psf_def] >> simp[psf_integral_def] >> irule EXTREAL_SUM_IMAGE_0 >> rw[])
        >- (qexists_tac `(nu,∅,(λi. ∅),(λi. 0))` >> simp[psf_empty,valid_psf_empty,psf_integral_empty])) >>
    `∑ (λi. ∫⁺ (space sa,subsets sa,mui i) f) (e INSERT s) =
        ∫⁺ (space sa,subsets sa,mui e) f + ∑ (λi. ∫⁺ (space sa,subsets sa,mui i) f) s` by (
        qspecl_then [`(λi. ∫⁺ (space sa,subsets sa,mui i) f)`,`s`,`e`]
            (fn th => assume_tac th >> rfs[DELETE_NON_ELEMENT_RWT] >> pop_assum irule) $
            SIMP_RULE bool_ss [GSYM RIGHT_FORALL_IMP_THM] EXTREAL_SUM_IMAGE_PROPERTY >>
        DISJ1_TAC >> rw[] >> irule pos_not_neginf >> irule pos_fn_integral_pos >> simp[]) >>
    pop_assum SUBST1_TAC >>
    last_x_assum $ qspecl_then [`sa`,`mui`,`λt. ∑ (C mui t) s`,`f`] assume_tac >>
    rfs[] >> pop_assum $ SUBST1_TAC o SYM >> irule pos_fn_integral_measure_add >> simp[] >>
    qspecl_then [`sa`,`mui`,`λt. ∑ (C mui t) s`,`s`] assume_tac measure_space_sum >> rfs[] >>
    qx_gen_tac `t` >> DISCH_TAC >>
    qspecl_then [`C mui t`,`s`,`e`]
        (fn th => assume_tac th >> rfs[DELETE_NON_ELEMENT_RWT] >> pop_assum irule) $
        SIMP_RULE bool_ss [GSYM RIGHT_FORALL_IMP_THM] EXTREAL_SUM_IMAGE_PROPERTY >>
    DISJ1_TAC >> rw[] >> irule pos_not_neginf >> fs[measure_space_def,positive_def]
QED

Theorem pos_fn_integral_measure_cmul:
    ∀sa mu nu c f. measure_space (space sa,subsets sa,mu) ∧ 0 ≤ c ∧
        (∀x. x ∈ space sa ⇒ 0 ≤ f x) ∧ (∀s. s ∈ subsets sa ⇒ nu s = Normal c * mu s) ⇒
        ∫⁺ (space sa,subsets sa,nu) f = Normal c * ∫⁺ (space sa,subsets sa,mu) f
Proof
    rw[] >> qspecl_then [`sa`,`mu`,`nu`,`Normal c`] assume_tac measure_space_cmul >>
    rfs[pos_fn_integral_alt] >> qmatch_abbrev_tac `_ = _ * sup p` >>
    `Normal c * sup p = sup {Normal c * x | p x}` by (
        irule sup_cmul_alt_real_loose >> simp[] >> qexists_tac `0` >> qunabbrev_tac `p` >>
        simp[] >> qexists_tac `(mu,∅,(λi. ∅),(λi. 0))` >>
        simp[psf_empty,valid_psf_empty,psf_integral_empty]) >>
    simp[] >> pop_assum kall_tac >> qunabbrev_tac `p` >>
    irule $ iffLR le_antisym >> CONJ_TAC >> irule sup_le_sup_imp >> rw[] >>
    rename [`(z,T) = _ msea`] >> `∃mnu s e a. msea = (mnu,s,e,a)` by metis_tac[ABS_PAIR_THM] >>
    fs[] >> rw[] >> rename [`∀s. s ∈ subsets sa ⇒ nu s = Normal c * mu s`] >>
    drule_all_then assume_tac psf_integral_measure_cmul
    >- (map_every (fn tm => qexists_tac tm >> simp[])
            [`Normal c * psf_integral mu s e a`,`psf_integral mu s e a`,`mu,s,e,a`])
    >- (pop_assum $ assume_tac o GSYM >>
        map_every (fn tm => qexists_tac tm >> simp[]) [`psf_integral nu s e a`,`nu,s,e,a`])
QED

Theorem pos_fn_integral_measure_suminf:
    ∀sa mun nu f. (∀n. measure_space (space sa,subsets sa,mun n)) ∧
        f ∈ Borel_measurable sa ∧ (∀x. x ∈ space sa ⇒ 0 ≤ f x) ∧
        (∀s. s ∈ subsets sa ⇒ nu s = suminf (C mun s)) ⇒
        ∫⁺ (space sa,subsets sa,nu) f = suminf (λn. ∫⁺ (space sa,subsets sa,mun n) f)
Proof
    rw[] >>
    `measure_space (space sa,subsets sa,suminf ∘ C mun)` by (
        irule measure_space_suminf >> qexists_tac `mun` >> simp[]) >>
    `∫⁺ (space sa,subsets sa,nu) f = ∫⁺ (space sa,subsets sa,suminf ∘ C mun) f` by (
        irule pos_fn_integral_cong_measure >>
        drule_all_then assume_tac measure_space_suminf >> simp[]) >>
    pop_assum SUBST1_TAC >>
    drule_then assume_tac $ cj 1 $ iffLR measure_space_def >> fs[] >>
    drule_all_then assume_tac pos_fn_sup_psf_seq >> fs[] >>
    qspecl_then [`(space sa,subsets sa,mun n)`,`f`,`si`,`ei`,`ai`]
        (assume_tac o GEN ``n:num``) pos_fn_psf_integral_convergence >>
    qspecl_then [`(space sa,subsets sa,suminf ∘ C mun)`,`f`,`si`,`ei`,`ai`]
        assume_tac pos_fn_psf_integral_convergence >>
    rfs[] >> NTAC 2 $ pop_assum kall_tac >> simp[IMAGE_DEF] >>
    `suminf (λn. sup {psf_integral (mun n) (si i) (ei i) (ai i) | i | T}) =
        sup {suminf (λn. psf_integral (mun n) (si i) (ei i) (ai i)) | i | T}` by (
        qspec_then `λi n. psf_integral (mun n) (si i) (ei i) (ai i)`
            (irule o SIMP_RULE (srw_ss ()) []) ext_suminf_sup_eq >> rw[]
        >- (qspec_then `(space sa,subsets sa,mun i)`
                (irule o SIMP_RULE (srw_ss ()) []) psf_integral_mono >>
            qexists_tac `sa` >> fs[valid_psf_seq_def,ext_mono_increasing_def])
        >- (qspec_then `(space sa,subsets sa,mun i)`
                (irule o SIMP_RULE (srw_ss ()) []) psf_integral_pos >>
            qexists_tac `sa` >> fs[valid_psf_seq_def] >> rw[psf_pos,SF SFY_ss])) >>
    pop_assum SUBST1_TAC >>
    `∀i. psf_integral (suminf ∘ C mun) (si i) (ei i) (ai i) =
        suminf (λn. psf_integral (mun n) (si i) (ei i) (ai i))` suffices_by simp[EXTENSION] >>
    rw[] >> irule psf_integral_measure_suminf >> qexists_tac `sa` >> simp[iffLR valid_psf_seq_def]
QED

Theorem pos_fn_integral_measure_suminf_le:
    ∀sa mun nu f c. (∀n. measure_space (space sa,subsets sa,mun n)) ∧
        f ∈ Borel_measurable sa ∧ (∀x. x ∈ space sa ⇒ 0 ≤ f x) ∧
        (∀s. s ∈ subsets sa ⇒ nu s = suminf (C mun s)) ⇒
        (∫⁺ (space sa,subsets sa,nu) f ≤ c ⇔
        ∀n. ∫⁺ (space sa,subsets sa,λs. ∑ (C mun s) (count n)) f ≤ c)
Proof
    rw[] >> drule_all_then SUBST1_TAC pos_fn_integral_measure_suminf >>
    qspecl_then [`space sa,subsets sa,mun n`,`f`]
        (assume_tac o GEN ``n:num``) pos_fn_integral_pos >> rfs[] >>
    qspec_then `(λn. ∫⁺ (space sa,subsets sa,mun n) f)`
        (fn th => simp[SIMP_RULE (srw_ss ()) [] th]) ext_suminf_le >>
    `∀n. ∫⁺ (space sa,subsets sa,(λs. ∑ (C mun s) (count n))) f =
        ∑ (λn. ∫⁺ (space sa,subsets sa,mun n) f) (count n)` by (rw[] >>
        irule pos_fn_integral_measure_sum >> fs[measure_space_def]) >>
    simp[]
QED

Theorem integral_zero_measure:
    ∀sa x f. sigma_algebra sa ⇒ ∫ (space sa,subsets sa,(λs. 0)) f = 0
Proof
    rw[integral_def] >> dxrule_then assume_tac pos_fn_integral_zero_measure >>
    simp[FN_PLUS_POS,FN_MINUS_POS]
QED

Theorem integral_fixed_state_measure:
    ∀sa x f. sigma_algebra sa ∧ x ∈ space sa ∧ f ∈ Borel_measurable sa ⇒
        ∫ (space sa,subsets sa,C 𝟙 x) f = f x
Proof
    rw[integral_def] >> irule EQ_TRANS >> qexists_tac `f⁺ x - f⁻ x` >>
    `∀x1 x2 x3 x4. x1 = x3 ∧ x2 = x4 ⇒ x1 - x2 = x3 - x4` by simp[] >> pop_assum $ irule_at Any >>
    simp[GSYM FN_DECOMP] >> NTAC 2 $ irule_at Any pos_fn_integral_fixed_state_measure >>
    simp[FN_PLUS_POS,FN_MINUS_POS,iffLR IN_MEASURABLE_BOREL_PLUS_MINUS]
QED

Theorem integral_measure_add:
    ∀sa mu nu mnu f. measure_space (space sa,subsets sa,mu) ∧
        measure_space (space sa,subsets sa,nu) ∧
        integrable (space sa,subsets sa,mu) f ∧ integrable (space sa,subsets sa,nu) f ∧
        (∀s. s ∈ subsets sa ⇒ mnu s = mu s + nu s) ⇒
        ∫ (space sa,subsets sa,mnu) f =
        ∫ (space sa,subsets sa,mu) f + ∫ (space sa,subsets sa,nu) f
Proof
    rw[integral_def] >>
    qspecl_then [`sa`,`mu`,`nu`,`mnu`] assume_tac pos_fn_integral_measure_add >>
    rfs[FN_MINUS_POS,FN_PLUS_POS,integrable_def] >> pop_assum kall_tac >>
    map_every
        (fn th => map_every
            (fn tml => (qspecl_then tml assume_tac) th)
            [[`(space sa,subsets sa,mu)`,`f`],[`(space sa,subsets sa,nu)`,`f`]])
        [pos_fn_integral_fn_plus_not_infty,pos_fn_integral_fn_minus_not_infty] >> rfs[] >>
    map_every (fn tm => Cases_on tm >> fs[])
        [`∫⁺ (space sa,subsets sa,mu) f⁺`,`∫⁺ (space sa,subsets sa,mu) f⁻`,
        `∫⁺ (space sa,subsets sa,nu) f⁺`,`∫⁺ (space sa,subsets sa,nu) f⁻`] >>
    rw[] >> simp[extreal_add_def,extreal_sub_def,REAL_ADD2_SUB2]
QED

Theorem integrable_measure_add:
    ∀sa mu nu mnu f. measure_space (space sa,subsets sa,mu) ∧
        measure_space (space sa,subsets sa,nu) ∧
        integrable (space sa,subsets sa,mu) f ∧ integrable (space sa,subsets sa,nu) f ∧
        (∀s. s ∈ subsets sa ⇒ mnu s = mu s + nu s) ⇒
        integrable (space sa,subsets sa,mnu) f
Proof
    rw[] >>
    qspecl_then [`sa`,`mu`,`nu`,`mnu`] assume_tac pos_fn_integral_measure_add >>
    rfs[FN_MINUS_POS,FN_PLUS_POS,integrable_def] >> pop_assum kall_tac >>
    map_every
        (fn th => map_every
            (fn tml => (qspecl_then tml assume_tac) th)
            [[`(space sa,subsets sa,mu)`,`f`],[`(space sa,subsets sa,nu)`,`f`]])
        [pos_fn_integral_fn_plus_not_infty,pos_fn_integral_fn_minus_not_infty] >> rfs[] >>
    map_every (fn tm => Cases_on tm >> fs[])
        [`∫⁺ (space sa,subsets sa,mu) f⁺`,`∫⁺ (space sa,subsets sa,mu) f⁻`,
        `∫⁺ (space sa,subsets sa,nu) f⁺`,`∫⁺ (space sa,subsets sa,nu) f⁻`] >>
    rw[] >> simp[extreal_add_def]
QED

Theorem integral_measure_cmul:
    ∀sa mu nu c f. measure_space (space sa,subsets sa,mu) ∧ integrable (space sa,subsets sa,mu) f ∧
        0 ≤ c ∧ (∀s. s ∈ subsets sa ⇒ nu s = Normal c * mu s) ⇒
        ∫ (space sa,subsets sa,nu) f = Normal c * ∫ (space sa,subsets sa,mu) f
Proof
    rw[integral_def] >>
    qspecl_then [`sa`,`mu`,`nu`,`c`] assume_tac pos_fn_integral_measure_cmul >>
    rfs[FN_MINUS_POS,FN_PLUS_POS,integrable_def] >> pop_assum kall_tac >>
    map_every (fn th => (qspecl_then [`(space sa,subsets sa,mu)`,`f`] assume_tac) th)
        [pos_fn_integral_fn_plus_not_infty,pos_fn_integral_fn_minus_not_infty] >> rfs[] >>
    map_every (fn tm => Cases_on tm >> fs[])
        [`∫⁺ (space sa,subsets sa,mu) f⁺`,`∫⁺ (space sa,subsets sa,mu) f⁻`] >>
    rw[] >> simp[extreal_mul_def,extreal_sub_def,REAL_SUB_LDISTRIB]
QED

Theorem integrable_measure_cmul:
    ∀sa mu nu c f. measure_space (space sa,subsets sa,mu) ∧ integrable (space sa,subsets sa,mu) f ∧
        0 ≤ c ∧ (∀s. s ∈ subsets sa ⇒ nu s = Normal c * mu s) ⇒
        integrable (space sa,subsets sa,nu) f
Proof
    rw[] >>
    qspecl_then [`sa`,`mu`,`nu`,`c`] assume_tac pos_fn_integral_measure_cmul >>
    rfs[FN_MINUS_POS,FN_PLUS_POS,integrable_def] >> pop_assum kall_tac >>
    map_every (fn th => (qspecl_then [`(space sa,subsets sa,mu)`,`f`] assume_tac) th)
        [pos_fn_integral_fn_plus_not_infty,pos_fn_integral_fn_minus_not_infty] >> rfs[] >>
    map_every (fn tm => Cases_on tm >> fs[])
        [`∫⁺ (space sa,subsets sa,mu) f⁺`,`∫⁺ (space sa,subsets sa,mu) f⁻`] >>
    rw[] >> simp[extreal_mul_def]
QED

(*---------------------------------------------------------------------------*)
(* Trivial stuff for Product Spaces *)
(*---------------------------------------------------------------------------*)

Theorem in_mspace_prod_measure_space:
    ∀m0 m1 z. z ∈ m_space (m0 × m1) ⇔ FST z ∈ m_space m0 ∧ SND z ∈ m_space m1
Proof
    simp[prod_measure_space_def]
QED

Theorem m_space_prod_measure_space:
    ∀m0 m1. m_space (m0 × m1) = m_space m0 × m_space m1
Proof
    simp[prod_measure_space_def]
QED

Theorem measurable_sets_prod_measure_space:
    ∀m0 m1. measurable_sets (m0 × m1) = subsets (sig_alg m0 × sig_alg m1)
Proof
    rw[prod_measure_space_def]
QED

Theorem sig_alg_prod_measure_space:
    ∀m0 m1. sig_alg (m0 × m1) = sig_alg m0 × sig_alg m1
Proof
    simp[prod_measure_space_def,prod_sigma_def,SIGMA_REDUCE]
QED

Theorem MEASURE_SPACE_CROSS:
    ∀m0 m1 s0 s1. measure_space m0 ∧ measure_space m1 ∧ s0 ∈ measurable_sets m0 ∧ s1 ∈ measurable_sets m1 ⇒
       s0 × s1 ∈ measurable_sets (m0 × m1)
Proof
    rw[prod_measure_space_def,prod_sigma_def] >> irule IN_SIGMA >> simp[prod_sets_def] >>
    qexistsl_tac [`s0`,`s1`] >> simp[]
QED

Theorem prob_space_alt:
    ∀p. prob_space p ⇔ measure_space p ∧ ∫⁺ p (λx. 1) = 1
Proof
    rw[prob_space_def] >> Cases_on `measure_space p` >> simp[] >>
    qspecl_then [`p`,`1`] mp_tac pos_fn_integral_const >> simp[]
QED

Theorem prob_space_density:
    ∀m f. measure_space m ∧ f ∈ Borel_measurable (m_space m,measurable_sets m) ∧
        (∀x. x ∈ m_space m ⇒ 0 ≤ f x) ∧ ∫⁺ m f = 1 ⇒ prob_space (density m f)
Proof
    rw[] >> simp[prob_space_alt] >> irule_at Any measure_space_density >> simp[] >>
    qspecl_then [`m`,`f`,`λx. 1`] mp_tac pos_fn_integral_density_clean >> simp[ETA_AX] >>
    DISCH_THEN irule >> irule IN_MEASURABLE_BOREL_CONST >> simp[] >> qexists_tac `1` >> simp[]
QED

Theorem prob_space_density_pos_fn_integral_pdf:
    ∀m f. measure_space m ∧ (∀x. x ∈ m_space m ⇒ 0 ≤ f x) ∧ prob_space (density m f) ⇒
        ∫⁺ m f = 1
Proof
    rw[prob_space_def,density_def,density_measure_def] >> pop_assum $ SUBST1_TAC o SYM >>
    irule pos_fn_integral_cong >> simp[indicator_fn_def]
QED

Theorem TONELLI_ALT:
    ∀m0 m1 f. sigma_finite_measure_space m0 ∧ sigma_finite_measure_space m1 ∧
        f ∈ Borel_measurable ((sig_alg m0) × (sig_alg m1)) ∧
        (∀s. s ∈ (m_space m0) × (m_space m1) ⇒ 0 ≤ f s) ⇒
        (∀y. y ∈ m_space m1 ⇒ (λx. f (x,y)) ∈ Borel_measurable (sig_alg m0)) ∧
        (∀x. x ∈ m_space m0 ⇒ (λy. f (x,y)) ∈ Borel_measurable (sig_alg m1)) ∧
        (λx. ∫⁺ m1 (λy. f (x,y))) ∈ Borel_measurable (sig_alg m0) ∧
        (λy. ∫⁺ m0 (λx. f (x,y))) ∈ Borel_measurable (sig_alg m1) ∧
        ∫⁺ (m0 × m1) f = ∫⁺ m1 (λy. ∫⁺ m0 (λx. f (x,y))) ∧
        ∫⁺ (m0 × m1) f = ∫⁺ m0 (λx. ∫⁺ m1 (λy. f (x,y)))
Proof
    rpt gen_tac >> strip_tac >>
    qspecl_then [`m_space m0`,`m_space m1`,`measurable_sets m0`,`measurable_sets m1`,
        `measure m0`,`measure m1`,`f`] mp_tac TONELLI >>
    simp[] >> DISCH_TAC >> fs[] >> NTAC 2 $ pop_assum $ SUBST1_TAC o SYM >> simp[]
QED

Theorem prod_measure_cross:
    ∀m0 m1 s0 s1. measure_space m0 ∧ measure_space m1 ∧ s0 ∈ measurable_sets m0 ∧ s1 ∈ measurable_sets m1 ⇒
        measure (m0 × m1) (s0 × s1) = measure m0 s0 * measure m1 s1
Proof
    rw[prod_measure_space_def,prod_measure_def,INDICATOR_FN_CROSS] >>
    irule EQ_TRANS >> qexists_tac `∫⁺ m1 (λy. measure m0 s0 * 𝟙 s1 y)` >>
    irule_at Any pos_fn_integral_cmul_indicator' >> simp[MEASURE_POSITIVE] >>
    irule_at Any pos_fn_integral_cong >> simp[] >>
    simp[GSYM FORALL_AND_THM,GSYM IMP_CONJ_THM] >> qx_gen_tac `y` >> strip_tac >>
    irule_at Any pos_fn_integral_pos >> irule_at Any le_mul >>
    simp[MEASURE_POSITIVE,INDICATOR_FN_POS,le_mul] >>
    `∫⁺ m0 (λx. 𝟙 s1 y * 𝟙 s0 x) = 𝟙 s1 y * measure m0 s0` suffices_by simp[mul_comm] >>
    irule_at Any pos_fn_integral_cmul_indicator' >> simp[INDICATOR_FN_POS]
QED

Theorem sigma_finite_measure_space_prod_measure:
    ∀m1 m2. sigma_finite_measure_space m1 ∧ sigma_finite_measure_space m2 ⇒
        sigma_finite_measure_space (m1 × m2)
Proof
    rw[] >> simp[sigma_finite_measure_space_def,measure_space_prod_measure] >>
    fs[sigma_finite_measure_space_def,sigma_finite_alt_exhausting_sequence] >>
    rename [`(m1 × m2)`,`exhausting_sequence (sig_alg m1) f`,`exhausting_sequence (sig_alg m2) g`] >>
    qexists_tac `λn. f n × g n` >> CONJ_TAC
    >- (qspecl_then [`m_space m1`,`m_space m2`,`measurable_sets m1`,`measurable_sets m2`,`f`,`g`] mp_tac
            exhausting_sequence_CROSS >>
        simp[] >> simp[exhausting_sequence_def,m_space_prod_measure_space] >> strip_tac >>
        fs[FUNSET] >> qx_gen_tac `n` >> simp[prod_measure_space_def,prod_sigma_def] >>
        irule $ SIMP_RULE (srw_ss ()) [SUBSET_DEF] SIGMA_SUBSET_SUBSETS >> simp[prod_sets_def])
    >- (simp[] >> fs[exhausting_sequence_def,FUNSET,GSYM lt_infty] >> simp[prod_measure_cross] >>
        qx_gen_tac `n` >> irule $ cj 2 mul_not_infty2 >> simp[MEASURE_POSITIVE,le_not_infty])
QED

Theorem measure_prod_measure_space_itr:
    ∀m0 m1 s. sigma_finite_measure_space m0 ∧ sigma_finite_measure_space m1 ∧
        s ∈ measurable_sets (m0 × m1) ⇒
        measure (m0 × m1) s = ∫⁺ m0 (λx. measure m1 {y | (x,y) ∈ s}) ∧
        ∀x. {y | (x,y) ∈ s} ∈ measurable_sets m1
Proof
    rpt gen_tac >> strip_tac >>
    `measure_space (m0 × m1)` by simp[measure_space_prod_measure] >>
    REVERSE CONJ_ASM2_TAC
    >- (qx_gen_tac `x` >> qspecl_then [`sig_alg m0`,`sig_alg m1`,`s`] mp_tac PROD_SIGMA_Y_SLICE >> simp[] >>
        DISCH_THEN $ irule_at Any >>
        simp[GSYM sig_alg_prod_measure_space,iffLR sigma_finite_measure_space_def,MEASURE_SPACE_SUBSET_CLASS]) >>
    `𝟙 s ∈ Borel_measurable (sig_alg (m0 × m1))` by (irule IN_MEASURABLE_BOREL_INDICATOR >>
        simp[] >> qexists_tac `s` >> simp[]) >>
    qspecl_then [`m_space m0`,`m_space m1`,`measurable_sets m0`,`measurable_sets m1`,
        `measure m0`,`measure m1`,`𝟙 s`] mp_tac TONELLI >>
    simp[GSYM sig_alg_prod_measure_space,INDICATOR_FN_POS] >> strip_tac >>
    simp[prod_measure_space_def,prod_measure_def] >> rfs[] >> NTAC 6 $ pop_assum kall_tac >>
    irule pos_fn_integral_cong >> fs[sigma_finite_measure_space_def] >>
    simp[GSYM FORALL_IMP_CONJ_THM] >> NTAC 2 strip_tac >> first_x_assum $ qspec_then `x` assume_tac >>
    simp[GSYM pos_fn_integral_indicator] >> `(λy. 𝟙 s (x,y)) = 𝟙 {y | (x,y) ∈ s}` by simp[indicator_fn_def] >>
    pop_assum SUBST1_TAC >> simp[] >> irule pos_fn_integral_pos >> simp[INDICATOR_FN_POS]
QED

(*---------------------------------------------------------------------------*)
(* Trivial stuff for Probability *)
(*---------------------------------------------------------------------------*)

Theorem indep_rv_expectation = indep_vars_expectation;

(* make simpset in trivialSimps *)
val prob_notation_simps =
    [prob_space_def,real_random_variable_def,random_variable_def,expectation_def,p_space_def,events_def,prob_def];

Theorem prob_re_sig_alg:
    ∀p. (p_space p,events p) = sig_alg p
Proof
    simp[p_space_def,events_def]
QED

val _ = mk_local_simp "prob_re_sig_alg";

Theorem PROB_SPACE_SIGMA_ALGEBRA:
    (∀p. prob_space (p:α m_space) ⇒ sigma_algebra (sig_alg p)) ∧
    (∀sa mu. prob_space ((space sa,subsets sa,mu):α m_space) ⇒ sigma_algebra sa) ∧
    (∀sp sts mu. prob_space ((sp,sts,mu):α m_space) ⇒ sigma_algebra (sp,sts))
Proof
    rw[prob_space_def,SF SFY_ss]
QED

val _ = mk_local_simp "PROB_SPACE_SIGMA_ALGEBRA";

Theorem PROB_CONG_AE:
    ∀p s t. prob_space p ∧ s ∈ events p ∧ t ∈ events p ∧ (AE x::p. x ∈ s ⇔ x ∈ t) ⇒
        prob p s = prob p t
Proof
    simp prob_notation_simps >> simp[MEASURE_CONG_AE]
QED

Theorem prob_space_not_empty:
    ∀p. prob_space p ⇒ p_space p ≠ ∅
Proof
    rw[prob_space_def,p_space_def] >> CCONTR_TAC >> fs[] >> rfs[MEASURE_EMPTY]
QED

Theorem prob_space_fixed_state_measure:
    ∀sa x. sigma_algebra sa ∧ x ∈ space sa ⇒ prob_space (space sa,subsets sa,C 𝟙 x)
Proof
    simp[prob_space_def,measure_space_fixed_state_measure] >>
    simp[m_space_def,measurable_sets_def,measure_def,indicator_fn_def,IN_APP]
QED

Theorem real_random_variable_fn_plus:
    ∀p X. prob_space p ∧ real_random_variable X p ⇒ real_random_variable X⁺ p
Proof
    rw[real_random_variable,p_space_def,events_def]
    >- fs[Once IN_MEASURABLE_BOREL_PLUS_MINUS] >> rw[fn_plus_def]
QED

Theorem real_random_variable_fn_minus:
    ∀p X. prob_space p ∧ real_random_variable X p ⇒ real_random_variable X⁻ p
Proof
    rw[real_random_variable,p_space_def,events_def]
    >- fs[Once IN_MEASURABLE_BOREL_PLUS_MINUS] >> rw[fn_minus_def] >>
    Cases_on `X x` >> rfs[extreal_ainv_def]
QED

Theorem expectation_pos_fn:
    ∀p X. prob_space p ∧ (∀x. x ∈ p_space p ⇒ 0 ≤ X x) ⇒ expectation p X = ∫⁺ p X
Proof
    rw[prob_space_def,p_space_def,expectation_def,integral_pos_fn]
QED

Theorem expectation_cong_AE:
    ∀p X Y. prob_space p ∧ (AE x::p. X x = Y x) ⇒ expectation p X = expectation p Y
Proof
    simp[prob_space_def,expectation_def,integral_cong_AE]
QED

Theorem expectation_sum:
    ∀p X J. prob_space p ∧ FINITE J ∧ (∀n. n ∈ J ⇒ real_random_variable (X n) p) ∧
        (∀n. n ∈ J ⇒ integrable p (X n)) ⇒
        expectation p (λx. ∑ (λi. X i x) J) = ∑ (λi. expectation p (X i)) J
Proof
    rw prob_notation_simps >> irule integral_sum >> simp[]
QED

Theorem INDEP_BIGUNION:
    ∀p s f. prob_space p ∧ (∀m n. m ≠ n ⇒ DISJOINT (f m) (f n)) ∧ (∀n. indep p s (f n)) ⇒
        indep p s (BIGUNION (IMAGE f 𝕌(:num)))
Proof
    rw[] >> fs[indep_def] >> CONJ_ASM1_TAC
    >- (irule EVENTS_COUNTABLE_UNION >> rw[SUBSET_DEF] >> fs[]) >>
    drule_then assume_tac PROB_SPACE_COUNTABLY_ADDITIVE >> simp[GSYM BIGUNION_IMAGE_INTER_LEFT] >>
    map_every (fn (pos,th,qel,ths) => irule_at pos th >> qexistsl_tac qel >> simp ths) [
        (Pos hd,EQ_TRANS,[`prob p s * suminf (prob p ∘ f)`],[]),
        (Pos hd,EQ_TRANS,[`suminf (λn. prob p s * (prob p ∘ f) n)`],[]),
        (Pos hd,EQ_TRANS,[`suminf (prob p ∘ (λn. s ∩ f n))`],[]),
        (Any,IRULER,[],[]),(Any,IRULER,[],[]),
        (Any,SIMP_RULE (srw_ss()) [] $ SPEC ``(g:α measure) ∘ (f:num -> α -> bool)`` ext_suminf_cmul,
            [],[PROB_POSITIVE]),
        (Any,iffLR COUNTABLY_ADDITIVE_PROB,[],[]),
        (Any,EQ_SYM,[],[]),(Any,iffLR COUNTABLY_ADDITIVE_PROB,[],[]),
        (Any,EVENTS_COUNTABLE_UNION,[],[])] >>
    simp[FUN_EQ_THM] >> fs[DISJOINT_ALT,SF SFY_ss] >> rw[SUBSET_DEF,FUNSET] >> simp[EVENTS_INTER]
QED

Theorem indep_rv_expectation_pos:
    ∀p X Y. prob_space p ∧ real_random_variable X p ∧ real_random_variable Y p ∧
        (∀x. x ∈ p_space p ⇒ 0 ≤ X x) ∧ (∀x. x ∈ p_space p ⇒ 0 ≤ Y x) ∧
        indep_vars p X Y Borel Borel ∧ integrable p X ∧ integrable p Y ⇒
        ∫⁺ p (λx. X x * Y x) = ∫⁺ p X * ∫⁺ p Y
Proof
    rw[] >> drule_all_then assume_tac indep_rv_expectation >> rfs[expectation_pos_fn] >>
    pop_assum $ SUBST1_TAC o SYM >> irule $ GSYM expectation_pos_fn >> rw[le_mul]
QED

Theorem indep_rv_integrable:
    ∀p X Y. prob_space p ∧ real_random_variable X p ∧ real_random_variable Y p ∧
        indep_vars p X Y Borel Borel ∧ integrable p X ∧ integrable p Y ⇒
        integrable p (λx. X x * Y x)
Proof
    rw[] >>
    `indep_vars p X⁺ Y⁺ Borel Borel ∧ indep_vars p X⁺ Y⁻ Borel Borel ∧
        indep_vars p X⁻ Y⁺ Borel Borel ∧ indep_vars p X⁻ Y⁻ Borel Borel` by (
        `(∀(Z: α -> extreal). Z⁺ = (λz. max 0 z) ∘ Z) ∧ (∀(Z:α -> extreal). Z⁻ = (λz. -min 0 z) ∘ Z)` by
            rw[FUN_EQ_THM,FN_PLUS_ALT',FN_MINUS_ALT'] >>
        simp[] >> NTAC 4 $ irule_at (Pos last) indep_rv_cong >> simp[iffLR real_random_variable_def] >>
        irule_at (Pos last) IN_MEASURABLE_BOREL_MINUS >>
        qexists_tac `λz. min 0 z` >> simp[SIGMA_ALGEBRA_BOREL] >>
        qspecl_then [`Borel`,`λx. 0`,`λx. x`]
            (irule_at Any o SIMP_RULE (srw_ss ()) []) IN_MEASURABLE_BOREL_MAX >>
        qspecl_then [`Borel`,`λx. 0`,`λx. x`]
            (irule_at Any o SIMP_RULE (srw_ss ()) []) IN_MEASURABLE_BOREL_MIN >>
        simp[SIGMA_ALGEBRA_BOREL,IN_MEASURABLE_BOREL_BOREL_I,IN_MEASURABLE_BOREL_CONST']) >>
    map_every (fn tms => qspecl_then tms assume_tac indep_rv_expectation_pos)
        [[`p`,`X⁺`,`Y⁺`],[`p`,`X⁺`,`Y⁻`],[`p`,`X⁻`,`Y⁺`],[`p`,`X⁻`,`Y⁻`]] >>
    rfs[iffLR prob_space_def,integrable_fn_plus,integrable_fn_minus,
        real_random_variable_fn_plus,real_random_variable_fn_minus,expectation_def,
        FN_PLUS_POS,FN_MINUS_POS] >>
    fs[integrable_def,prob_space_def] >> irule_at Any IN_MEASURABLE_BOREL_MUL >>
    qexistsl_tac [`Y`,`X`] >> simp[] >> fs[real_random_variable_def,p_space_def] >>
    simp[FN_PLUS_FFMUL,FN_MINUS_FFMUL] >>
    `∫⁺ p (λx. X⁺ x * Y⁺ x + X⁻ x * Y⁻ x) = ∫⁺ p (λx. X⁺ x * Y⁺ x) + ∫⁺ p (λx. X⁻ x * Y⁻ x) ∧
      ∫⁺ p (λx. X⁺ x * Y⁻ x + X⁻ x * Y⁺ x) = ∫⁺ p (λx. X⁺ x * Y⁻ x) + ∫⁺ p (λx. X⁻ x * Y⁺ x)` by (
        map_every (fn tms => qspecl_then tms
            (irule_at Any o SIMP_RULE (srw_ss ()) []) pos_fn_integral_add)
            [[`p`,`λx. X⁺ x * Y⁺ x`,`λx. X⁻ x * Y⁻ x`],[`p`,`λx. X⁺ x * Y⁻ x`,`λx. X⁻ x * Y⁺ x`]] >>
        simp[FN_PLUS_POS,FN_MINUS_POS,le_mul] >>
        map_every (fn qex => irule_at (Pos last) IN_MEASURABLE_BOREL_MUL >>
            qexistsl_tac qex >> simp[iffLR IN_MEASURABLE_BOREL_PLUS_MINUS])
            [[`Y⁻`,`X⁻`],[`Y⁺`,`X⁺`],[`Y⁺`,`X⁻`],[`Y⁻`,`X⁺`]] >>
        simp[FN_PLUS_NOT_INFTY,FN_MINUS_NOT_INFTY,FN_PLUS_NOT_NEG_INFTY,FN_MINUS_NOT_NEG_INFTY]) >>
    NTAC 6 $ pop_assum SUBST1_TAC >>
    Cases_on `∫⁺ p X⁺` >> Cases_on `∫⁺ p Y⁺` >> Cases_on `∫⁺ p X⁻` >> Cases_on `∫⁺ p Y⁻` >>
    rfs[pos_fn_integral_fn_plus_not_infty,pos_fn_integral_fn_minus_not_infty] >>
    simp[extreal_mul_def,extreal_add_def]
QED

Theorem real_random_variable_prod:
    ∀p X J. prob_space p ∧ FINITE J ∧ (∀n. n ∈ J ⇒ real_random_variable (X n) p) ⇒
        real_random_variable (λx. ∏ (C X x) J) p
Proof
    rw[] >> fs[real_random_variable,p_space_def,events_def,prob_space_def] >>
    rfs[EXTREAL_PROD_IMAGE_NOT_INFTY] >> irule IN_MEASURABLE_BOREL_PROD >> simp[] >>
    qexistsl_tac [`X`,`J`] >> simp[C_DEF]
QED

Theorem indep_vars_subset:
    ∀p X J L. prob_space p ∧ FINITE J ∧ L ⊆ J ∧ indep_vars p X (K Borel) J ⇒ indep_vars p X (K Borel) L
Proof
    rw[] >> fs[indep_vars_def,DFUNSET,indep_events_def] >> rw[] >>
    `(∀x. x ∈ J ⇒ (λx. if x ∈ L then E x else ∅) x ∈ subsets Borel)` by
        rw[BOREL_MEASURABLE_SETS_EMPTY] >>
    last_x_assum $ dxrule_then $ qspec_then `N` assume_tac >> rfs[SUBSET_DEF] >> pop_assum mp_tac >>
    qmatch_abbrev_tac `x1 = x2 ⇒ x3 = x4` >> `x1 = x3 ∧ x2 = x4` suffices_by simp[] >>
    UNABBREV_ALL_TAC >> NTAC 2 $ irule_at (Pos hd) IRULER >>
    irule_at Any EXTREAL_PROD_IMAGE_EQ >> irule_at Any IMAGE_CONG >> simp[]
QED

Theorem indep_vars_indep_rv_prod:
    ∀p X J e. prob_space p ∧ FINITE J ∧ e ∉ J ∧
        (∀n. n = e ∨ n ∈ J ⇒ real_random_variable (X n) p) ∧ indep_vars p X (K Borel) (e INSERT J) ⇒
        indep_vars p (X e) (λx. ∏ (C X x) J) Borel Borel
Proof
    rw[] >> fs[indep_rv_def] >> Cases_on `J = ∅`
    >- (fs[EXTREAL_PROD_IMAGE_EMPTY,indep_rv_def,indep_def] >>
        qspecl_then [`p`,`Normal 1`] assume_tac real_random_variable_const >> rfs[normal_1] >>
        rw[] >> fs[real_random_variable,IN_MEASURABLE] >>
        `PREIMAGE (λx. 1) b = (∅ : α -> bool) ∨ PREIMAGE (λx. 1) b = 𝕌(:α)` by (
            simp[PREIMAGE_def] >> Cases_on `1 ∈ b` >> simp[]) >>
        pop_assum SUBST1_TAC >> simp[PROB_EMPTY,PROB_UNIV] >> simp[INTER_DEF,GSYM CONJ_ASSOC]) >>
    `subsets (sigma (p_space p)
      {BIGINTER (IMAGE (λn. PREIMAGE (X n) (s n) ∩ p_space p) J) | s ∈ (UNIV → subsets Borel)}) ⊆
      {b | ∀a. a ∈ subsets Borel ⇒ indep p (PREIMAGE (X e) a ∩ p_space p) b}` suffices_by (
        rw[] >> fs[SUBSET_DEF] >> first_x_assum irule >> simp[] >> gs prob_notation_simps >>
        qmatch_abbrev_tac `_ ∈ subsets sa` >> `m_space p = space sa` by simp[Abbr`sa`,SPACE_SIGMA] >>
        `sigma_algebra sa` by (simp[Abbr `sa`] >> irule SIGMA_ALGEBRA_SIGMA >>
            rw[subset_class_def,SUBSET_DEF] >> fs[IN_BIGUNION_IMAGE] >>
            rename[`z ∈ m_space p`] >> fs[GSYM MEMBER_NOT_EMPTY] >>
            pop_assum $ qspec_then `PREIMAGE (X x) (s x) ∩ m_space p` assume_tac >>
            rfs[] >> pop_assum $ irule o cj 2 >> qexists_tac `x` >> simp[]) >>
        qspecl_then [`sa`,`Borel`,`λx. ∏ (C X x) J`] mp_tac $ iffLR IN_MEASURABLE >>
        simp[SIGMA_ALGEBRA_BOREL,FUNSET,SPACE_BOREL] >> disch_then irule >> simp[] >>
        irule IN_MEASURABLE_BOREL_PROD >> simp[] >> qexistsl_tac [`X`,`J`] >> simp[C_DEF] >>
        rw[Abbr`sa`,IN_MEASURABLE,SPACE_SIGMA,SIGMA_ALGEBRA_BOREL,FUNSET,SPACE_BOREL] >>
        irule IN_SIGMA >> simp[] >> qexists_tac `λn. if n = i then s else UNIV` >> REVERSE CONJ_TAC
        >- (rw[] >> simp[SYM SPACE_BOREL,SIGMA_ALGEBRA_BOREL,SIGMA_ALGEBRA_SPACE]) >>
        rw[Once EXTENSION,IN_BIGINTER_IMAGE] >> eq_tac >> rw[] >- rw[] >>
        pop_assum $ qspec_then `i` mp_tac >> simp[]) >>
    `∀X. real_random_variable X p ⇒ ∀r. r ∈ subsets Borel ⇒ PREIMAGE X r ∩ p_space p ∈ events p` by (
        rw (IN_MEASURABLE::prob_notation_simps)) >>
    irule PI_LAMBDA_THM >> rw[dynkin_system_def,pi_system_def,SUBSET_DEF]
    >- (rw[subset_class_def,indep_def] >> irule PROB_SPACE_SUBSET_PSPACE >> simp[] >>
        pop_assum $ irule o cj 1 >> qexists_tac `∅` >> simp[BOREL_MEASURABLE_SETS_EMPTY])
    >- (irule INDEP_SYM >> irule INDEP_SPACE >> simp[])
    >- (irule INDEP_COMPL >> simp[])
    >- (fs[FUNSET] >> irule INDEP_BIGUNION >> simp[])
    >- (rw[subset_class_def,indep_def] >> irule PROB_SPACE_SUBSET_PSPACE >> simp[] >>
        irule EVENTS_BIGINTER_FN >> rw[finite_countable,SUBSET_DEF,IN_IMAGE] >> gs[FUNSET])
    >- (simp[GSYM MEMBER_NOT_EMPTY] >> qexists_tac `K ∅` >> simp[FUNSET,BOREL_MEASURABLE_SETS_EMPTY])
    >- (rename [`BIGINTER (IMAGE (λn. PREIMAGE (X n) (s n) ∩ p_space p) J) ∩
            BIGINTER (IMAGE (λn. PREIMAGE (X n) (t n) ∩ p_space p) J)`] >>
        qexists_tac `λn. s n ∩ t n` >> fs[FUNSET,SIGMA_ALGEBRA_BOREL,SIGMA_ALGEBRA_INTER] >>
        rw[Once EXTENSION,IN_BIGINTER_IMAGE] >> eq_tac >> rw[SF SFY_ss])
    >- (fs[indep_def,indep_vars_def,indep_events_def] >> CONJ_TAC
        >- (irule_at Any EVENTS_BIGINTER_FN >> rw[finite_countable,SUBSET_DEF,IN_IMAGE] >> gs[FUNSET]) >>
        gs[FUNSET,DFUNSET] >> irule EQ_TRANS >>
        last_x_assum $ qspec_then `λn. if n = e then a else s n` assume_tac >>
        `(∀x. x = e ∨ x ∈ J ⇒ (λn. if n = e then a else s n) x ∈ subsets Borel)` by rw[] >>
        first_x_assum $ dxrule_then (qspec_then `e INSERT J` assume_tac) >>
        rfs[EXTREAL_PROD_IMAGE_THM,DELETE_NON_ELEMENT_RWT] >> pop_assum mp_tac >>
        qmatch_abbrev_tac `x1 = x2 ⇒ x3 = x4` >> `x1 = x3 ∧ x2 = x4` suffices_by simp[] >>
        UNABBREV_ALL_TAC >>
        map_every (fn (pos,th) => irule_at pos th) [
            (Pos hd,IRULER),(Pos hd,IRULER),(Pos hd,IRULER), (Pos last,IRULER),
            (Pos hd,EXTREAL_PROD_IMAGE_EQ),(Pos last,IMAGE_CONG)] >>
        simp[GSYM FORALL_IMP_CONJ_THM] >> rw[])
QED

Theorem indep_vars_integrable:
    ∀p X J. prob_space p ∧ FINITE J ∧ (∀n. n ∈ J ⇒ real_random_variable (X n) p) ∧
        indep_vars p X (K Borel) J ∧ (∀n. n ∈ J ⇒ integrable p (X n)) ⇒
        integrable p (λx. ∏ (C X x) J)
Proof
    rw[] >> NTAC 3 $ pop_assum mp_tac >> Induct_on `J` >> rw[]
    >- fs[EXTREAL_PROD_IMAGE_EMPTY,SYM normal_1,prob_space_def,integrable_const] >>
    simp[EXTREAL_PROD_IMAGE_PROPERTY,DELETE_NON_ELEMENT_RWT] >>
    qspecl_then [`p`,`X e`,`λx. ∏ (C X x) J`]
        (irule o SIMP_RULE (srw_ss ()) []) indep_rv_integrable >>
    simp[] >> last_x_assum $ irule_at (Pos hd) >> simp[real_random_variable_prod] >>
    map_every (irule_at (Pos last)) [indep_vars_indep_rv_prod,indep_vars_subset] >>
    qexists_tac `e INSERT J` >> rw[] >> simp[]
QED

Theorem indep_vars_expectation:
    ∀p X J. prob_space p ∧ FINITE J ∧ (∀n. n ∈ J ⇒ real_random_variable (X n) p) ∧
        indep_vars p X (K Borel) J ∧ (∀n. n ∈ J ⇒ integrable p (X n)) ⇒
        expectation p (λx. ∏ (C X x) J) = ∏ (expectation p ∘ X) J
Proof
    rw[] >> NTAC 3 $ pop_assum mp_tac >> Induct_on `J` >> rw[]
    >- simp[EXTREAL_PROD_IMAGE_EMPTY,SYM normal_1,expectation_const] >>
    simp[EXTREAL_PROD_IMAGE_PROPERTY,DELETE_NON_ELEMENT_RWT] >>
    irule EQ_TRANS >> qexists_tac `expectation p (X e) * expectation p (λx. ∏ (C X x) J)` >>
    qspecl_then [`p`,`X e`,`λx. ∏ (C X x) J`]
        (irule_at Any o SIMP_RULE (srw_ss ()) []) indep_rv_expectation >>
    irule_at (Pos last) IRULER >> last_x_assum $ irule_at (Pos hd) >> simp[real_random_variable_prod] >>
    map_every (irule_at (Pos last)) [indep_vars_integrable,indep_vars_indep_rv_prod,indep_vars_subset] >>
    qexists_tac `e INSERT J` >> rw[] >> simp[]
QED

(* Markov Kernels *)

Definition sub_prob_space_def:
    sub_prob_space p ⇔ measure_space p ∧ measure p (m_space p) ≤ 1
End

Theorem sub_prob_space_finite_measure_space:
    ∀p. sub_prob_space p ⇒ finite_measure_space p
Proof
    rw[sub_prob_space_def,finite_measure_space_def,finite_def] >>
    irule let_trans >> qexists_tac `Normal 1` >> simp[normal_1]
QED

Theorem prob_space_sub_prob_space:
    ∀p. prob_space p ⇒ sub_prob_space p
Proof
    rw[prob_space_def,sub_prob_space_def]
QED

Theorem prob_space_finite_measure_space:
    ∀p. prob_space p ⇒ finite_measure_space p
Proof
    rw[prob_space_sub_prob_space,sub_prob_space_finite_measure_space]
QED

Theorem prob_space_sigma_finite_measure_space:
    ∀p. prob_space p ⇒ sigma_finite_measure_space p
Proof
    simp[prob_space_finite_measure_space,finite_measure_space_sigma_finite]
QED

Theorem prob_space_measure_space:
    ∀p. prob_space p ⇒ measure_space p
Proof
    simp[prob_space_def]
QED

Definition stochastic_kernel_def:
    stochastic_kernel sa = {p | sigma_algebra sa ∧
        (∀s. s ∈ space sa ⇒ sub_prob_space (space sa,subsets sa,(λA. p s A))) ∧
        (∀A. A ∈ subsets sa ⇒ (λs. p s A) ∈ Borel_measurable sa)}
End

Theorem stochastic_kernel_alt:
    ∀sa p. p ∈ stochastic_kernel sa ⇔ sigma_algebra sa ∧
        (∀s. s ∈ space sa ⇒ sub_prob_space (space sa,subsets sa,p s)) ∧
        (∀A. A ∈ subsets sa ⇒ C p A ∈ Borel_measurable sa)
Proof
    simp[stochastic_kernel_def,C_DEF,GSYM o_DEF,GSYM I_EQ_IDABS] >> simp[o_DEF]
QED

Theorem stochastic_kernel_transition_kernel:
    ∀sa p. p ∈ stochastic_kernel sa ⇒ p ∈ transition_kernel sa
Proof
    simp[stochastic_kernel_alt,transition_kernel_alt,sub_prob_space_def]
QED

Theorem stochastic_kernel_alt_bounds:
    ∀sa p. p ∈ stochastic_kernel sa ⇔ p ∈ transition_kernel sa ∧
        ∀s A. s ∈ space sa ∧ A ∈ subsets sa ⇒ p s A ≤ 1
Proof
    rw[] >> eq_tac >> simp[stochastic_kernel_transition_kernel] >>
    simp[stochastic_kernel_alt,sub_prob_space_def,iffLR transition_kernel_alt,SF SFY_ss] >> rw[]
    >- (irule le_trans >> qexists_tac `p s (space sa)` >>
        last_x_assum $ dxrule_then assume_tac >> fs[] >>
        dxrule_then assume_tac measure_upper_bound >> rfs[])
    >- (first_x_assum irule >> simp[iffLR transition_kernel_alt,SF SFY_ss,SIGMA_ALGEBRA_SPACE])
QED

Theorem stochastic_kernel_bounded_transition_kernel:
    ∀sa p. p ∈ stochastic_kernel sa ⇒ p ∈ bounded_transition_kernel sa
Proof
    rw[stochastic_kernel_alt_bounds,bounded_transition_kernel_alt_bounds] >>
    qexists_tac `1` >> simp[normal_1]
QED

Definition markov_kernel_def:
    markov_kernel sa = {p | sigma_algebra sa ∧
        (∀s. s ∈ space sa ⇒ prob_space (space sa,subsets sa,(λA. p s A))) ∧
        (∀A. A ∈ subsets sa ⇒ (λs. p s A) ∈ Borel_measurable sa)}
End

Theorem markov_kernel_alt:
    ∀sa p. p ∈ markov_kernel sa ⇔ sigma_algebra sa ∧
        (∀s. s ∈ space sa ⇒ prob_space (space sa,subsets sa,p s)) ∧
        (∀A. A ∈ subsets sa ⇒ C p A ∈ Borel_measurable sa)
Proof
    simp[markov_kernel_def,C_DEF,GSYM o_DEF,GSYM I_EQ_IDABS] >> simp[o_DEF]
QED

Theorem markov_kernel_stochastic_kernel:
    ∀sa p. p ∈ markov_kernel sa ⇒ p ∈ stochastic_kernel sa
Proof
    rw[markov_kernel_alt,stochastic_kernel_alt,prob_space_sub_prob_space]
QED

Theorem markov_kernel_bounded_transition_kernel:
    ∀sa p. p ∈ markov_kernel sa ⇒ p ∈ bounded_transition_kernel sa
Proof
    rw[markov_kernel_stochastic_kernel,stochastic_kernel_bounded_transition_kernel]
QED

Theorem markov_kernel_transition_kernel:
    ∀sa p. p ∈ markov_kernel sa ⇒ p ∈ transition_kernel sa
Proof
    rw[markov_kernel_stochastic_kernel,stochastic_kernel_transition_kernel]
QED

Theorem markov_kernel_alt_bounds:
    ∀sa p. p ∈ markov_kernel sa ⇔ p ∈ transition_kernel sa ∧
        ∀s. s ∈ space sa ⇒ p s (space sa) = 1
Proof
    rw[] >> eq_tac >> simp[markov_kernel_transition_kernel] >>
    simp[markov_kernel_alt,prob_space_def,iffLR transition_kernel_alt,SF SFY_ss]
QED

val _ = export_theory();
