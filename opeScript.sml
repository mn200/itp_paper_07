open HolKernel Parse boolLib bossLib;
open simpLib;
open markerTheory;
open combinTheory;
open pairTheory;
open pred_setTheory;
open listTheory;
open arithmeticTheory;
open realTheory;
open realLib;
open limTheory;
open seqTheory;
open transcTheory;
open real_sigmaTheory;
open extrealTheory;
open util_probTheory;
open sigma_algebraTheory;
open measureTheory;
open borelTheory;
open lebesgueTheory;
open martingaleTheory;
open probabilityTheory;
open trivialTheory;
open trivialSimps;
open pispaceTheory;
open pispaceSimps;
open hoeffdingTheory;

val _ = new_theory "ope";

val _ = reveal "C";

val _ = augment_srw_ss [TRIVIAL_ss];

val name_to_thname = fn s => ({Thy = "ope", Name = s}, DB.fetch "ope" s);

Theorem importance_sampling:
    ∀sa mu nu lam p q f.
        measure_space (space sa,subsets sa,mu) ∧ measure_space (space sa,subsets sa,nu) ∧
        measure_space (space sa,subsets sa,lam) ∧ p ∈ rn_derivative sa mu lam ∧
        q ∈ rn_derivative sa nu lam ∧ (AE x::(space sa,subsets sa,lam). q x ≠ +∞) ∧
        (∀x. x ∈ space sa ∧ q x = 0 ⇒ p x = 0) ∧ f ∈ Borel_measurable sa ⇒
        expectation (space sa,subsets sa,nu) (λx. p x * (q x)⁻¹ * f x) =
        expectation (space sa,subsets sa,mu) f
Proof
    rw[expectation_def] >>
    `(λx. p x * (q x)⁻¹ * f x) ∈ Borel_measurable sa` by (irule IN_MEASURABLE_BOREL_TIMES' >>
        simp[SF SFY_ss] >> qexistsl_tac [`λx. p x * (q x)⁻¹`,`f`] >> simp[] >>
        irule IN_MEASURABLE_BOREL_EQ' >> qexists_tac `λx. p x * ((q x)⁻¹ * 𝟙 {y | q y ≠ 0} x)` >>
        irule_at Any IN_MEASURABLE_BOREL_TIMES' >> qexistsl_tac [`λx. (q x)⁻¹ * 𝟙 {y | q y ≠ 0} x`,`p`] >>
        simp[SF SFY_ss,iffLR in_rn_derivative] >> irule_at Any IN_MEASURABLE_BOREL_INV >>
        qexists_tac `q` >> rw[SF SFY_ss,iffLR in_rn_derivative,indicator_fn_def] >> fs[]) >>
    map_every (fn tms => qspecl_then tms assume_tac rn_derivative_change >> rfs[])
        [[`sa`,`mu`,`lam`,`p`,`f`],[`sa`,`nu`,`lam`,`q`,`λx. p x * (q x)⁻¹ * f x`]] >>
    NTAC 2 $ pop_assum kall_tac >> irule integral_cong_AE >> simp[mul_assoc] >>
    qspecl_then [`(space sa,subsets sa,lam)`,`λx. q x ≠ +∞`,`λx. q x * p x * (q x)⁻¹ * f x = p x * f x`]
        (irule o SIMP_RULE (srw_ss ()) []) AE_subset >>
    rw[] >> `q x * p x * (q x)⁻¹ = p x` suffices_by simp[] >>
    Cases_on `q x = 0` >> simp[] >> simp[Once mul_comm,mul_assoc] >>
    `(q x)⁻¹ * q x = 1` suffices_by simp[] >> irule mul_linv >>
    fs[rn_derivative_def,SYM normal_0] >> CCONTR_TAC >> gs[] >>
    qpat_x_assum `∀x. x ∈ space sa ⇒ Normal 0 ≤ q x` $ dxrule_then assume_tac >> rfs[]
QED

Theorem importance_sampling_rn_derivative:
    ∀m p q f. measure_space m ∧
        p ∈ Borel_measurable (sig_alg m) ∧ (∀x. x ∈ m_space m ⇒ 0 ≤ p x) ∧
        q ∈ Borel_measurable (sig_alg m) ∧ (∀x. x ∈ m_space m ⇒ 0 ≤ q x) ∧
        (AE x::m. q x ≠ +∞) ∧ (∀x. x ∈ m_space m ∧ q x = 0 ⇒ p x = 0) ∧
        f ∈ Borel_measurable (sig_alg m) ⇒
        expectation (density m q) (λx. p x * (q x)⁻¹ * f x) = expectation (density m p) f
Proof
    rw[] >>
    `measure_space (density m p) ∧ measure_space (density m q)` by (rw[] >>
        irule measure_space_density >> simp[]) >>
    fs[density_def] >> qspec_then `sig_alg m` (irule o SIMP_RULE (srw_ss ()) []) importance_sampling >>
    simp[] >> qexists_tac `measure m` >> simp[rn_derivative_def]
QED

(*
    With proper Radon-Nikodym Theorem, (AE x::m. (nu / m) x < +∞) is unnecessary
*)
Theorem importance_sampling_measure:
    ∀m mu nu f. sigma_finite_measure_space m ∧
        measure_space (m_space m,measurable_sets m,mu) ∧ mu ≪ m ∧
        measure_space (m_space m,measurable_sets m,nu) ∧ nu ≪ m ∧
        (AE x::m. (nu / m) x ≠ +∞) ∧ (∀x. x ∈ m_space m ∧ (nu / m) x = 0 ⇒ (mu / m) x = 0) ∧
        f ∈ Borel_measurable (sig_alg m) ⇒
        expectation (m_space m,measurable_sets m,nu) (λx. (mu / m) x * ((nu / m) x)⁻¹ * f x) =
        expectation (m_space m,measurable_sets m,mu) f
Proof
    rw[] >> qspec_then `sig_alg m` (irule o SIMP_RULE (srw_ss ()) []) importance_sampling >>
    simp[] >> qexists_tac `measure m` >> simp[RN_deriv_exists]
QED

(* tsnoc *)
Datatype:
    traj = init σ | tcons traj ω α σ ρ
End

Definition num_steps_def:
    num_steps (init s) = 0 ∧
    num_steps (tcons (h: (α,ρ,σ,ω) traj) w a s r) = SUC (num_steps h)
End

Definition traj_n_gen_def:
    traj_n_gen 0 (sg: σ) (og: ω) (ag: α) (rg: ρ) = init sg ∧
    traj_n_gen (SUC n) sg og ag rg = tcons (traj_n_gen n sg og ag rg) og ag sg rg
End

Definition traj_inf_gen_def:
    (traj_inf_gen sg og ag rg (init s) ⇔ s = sg) ∧
    (traj_inf_gen sg og ag rg (tcons (h: (α,ρ,σ,ω) traj) w a s r) ⇔
        w = og ∧ a = ag ∧ s = sg ∧ r = rg ∧ traj_inf_gen sg og ag rg h)
End

Theorem in_traj_inf_gen:
    (∀(sg:σ) (og:ω) (ag:α) (rg:ρ) s. init s ∈ traj_inf_gen sg og ag rg ⇔ s = sg) ∧
    (∀(sg:σ) (og:ω) (ag:α) (rg:ρ) h w a s r. tcons h w a s r ∈ traj_inf_gen sg og ag rg ⇔
        w = og ∧ a = ag ∧ s = sg ∧ r = rg ∧ h ∈ traj_inf_gen sg og ag rg)
Proof
    simp[IN_APP,traj_inf_gen_def]
QED

Theorem traj_inf_gen_alt:
    ∀(sg:σ) (og:ω) (ag:α) (rg:ρ). traj_inf_gen sg og ag rg = IMAGE (λn. traj_n_gen n sg og ag rg) UNIV
Proof
    rw[] >> simp[EXTENSION] >> qx_gen_tac `h` >>
    Induct_on `h` >> rw[in_traj_inf_gen] >> eq_tac >> strip_tac
    >- (qexists_tac `0` >> simp[traj_n_gen_def])
    >- (Cases_on `n` >> fs[traj_n_gen_def])
    >- (qexists_tac `SUC n` >> simp[traj_n_gen_def])
    >- (Cases_on `n` >> gvs[traj_n_gen_def] >> rename [`traj_n_gen n sg og ag rg`] >>
        qexists_tac `n` >> simp[])
QED

Theorem traj_n_gen_in_traj_inf_gen:
    ∀n (sg:σ) (og:ω) (ag:α) (rg:ρ). traj_n_gen n sg og ag rg ∈ traj_inf_gen sg og ag rg
Proof
    rpt gen_tac >> Induct_on `n` >> simp[traj_n_gen_def,in_traj_inf_gen]
QED

Definition traj_cross_def:
    (traj_cross (init ss) (init s) ⇔ s ∈ ss) ∧
    (traj_cross (init ss) (tcons (h: (α,ρ,σ,ω) traj) w a s r) ⇔ F) ∧
    (traj_cross (tcons hs ws as ss rs) (init s) ⇔ F) ∧
    (traj_cross (tcons hs ws as ss rs) (tcons h w a s r) ⇔
        w ∈ ws ∧ a ∈ as ∧ s ∈ ss ∧ r ∈ rs ∧ traj_cross hs h)
End

Theorem in_traj_cross:
    (∀ss s. (init s):((α,ρ,σ,ω) traj) ∈ traj_cross (init ss) ⇔ s ∈ ss) ∧
    (∀ss (h: (α,ρ,σ,ω) traj) w a s r. tcons h w a s r ∉ traj_cross (init ss)) ∧
    (∀hs ws as ss rs s. (init s):((α,ρ,σ,ω) traj) ∉ traj_cross (tcons hs ws as ss rs)) ∧
    (∀hs ws as ss rs (h: (α,ρ,σ,ω) traj) w a s r. tcons h w a s r ∈ traj_cross (tcons hs ws as ss rs) ⇔
        w ∈ ws ∧ a ∈ as ∧ s ∈ ss ∧ r ∈ rs ∧ h ∈ traj_cross hs)
Proof
    simp[GSYM FORALL_AND_THM,RIGHT_AND_FORALL_THM] >> rpt gen_tac >>
    `∀(h: (α,ρ,σ,ω) traj) hs. h ∈ traj_cross hs ⇔ traj_cross hs h` by simp[IN_APP] >>
    simp[traj_cross_def]
QED

Theorem traj_cross_empty:
    (∀ss. traj_cross (init ss) = (∅ : (α,ρ,σ,ω) traj -> bool) ⇔ ss = ∅) ∧
    (∀hs ws as ss rs. traj_cross (tcons hs ws as ss rs) = (∅ : (α,ρ,σ,ω) traj -> bool) ⇔
        ws = ∅ ∨ as = ∅ ∨ ss = ∅ ∨ rs = ∅ ∨ traj_cross hs = ∅)
Proof
    rw[] >> eq_tac >> CONV_TAC CONTRAPOS_CONV >> simp[GSYM MEMBER_NOT_EMPTY] >> DISCH_TAC
    >- (fs[] >> rename [`s ∈ ss`] >> qexists_tac `init s` >> simp[in_traj_cross])
    >- (fs[] >> Cases_on `x` >> fs[in_traj_cross] >> qexists_tac `s` >> simp[])
    >- (fs[] >> rename [`traj_cross (tcons hs ws as ss rs)`,
            `w ∈ ws`,`a ∈ as`,`s ∈ ss`,` r ∈ rs`,`h ∈ traj_cross hs`] >>
        qexists_tac `tcons h w a s r` >> simp[in_traj_cross])
    >- (fs[] >> Cases_on `x` >> fs[in_traj_cross] >> simp[SF SFY_ss])
QED

Theorem traj_cross_eq:
    ∀hs gs. traj_cross hs = traj_cross gs ⇔ hs = gs ∨
        (traj_cross hs = (∅ : (α,ρ,σ,ω) traj -> bool) ∧ traj_cross gs = ∅)
Proof
    rw[] >> eq_tac >> rw[] >> fs[] >> Cases_on `traj_cross gs = ∅` >> simp[] >>
    last_x_assum mp_tac >> qid_spec_tac `hs` >> Induct_on `gs` >> rw[] >> Cases_on `hs` >> simp[]
    >- (rename [`hss = gss`] >> fs[EXTENSION] >> qx_gen_tac `s` >>
        pop_assum $ qspec_then `init s` assume_tac >> fs[in_traj_cross])
    >- (fs[GSYM MEMBER_NOT_EMPTY] >> rename [`h ∈ _`] >> pop_assum mp_tac >> simp[EXTENSION] >>
        qexists_tac `h` >> simp[] >> Cases_on `h` >> fs[in_traj_cross])
    >- (fs[GSYM MEMBER_NOT_EMPTY] >> rename [`h ∈ _`] >> pop_assum mp_tac >> simp[EXTENSION] >>
        qexists_tac `h` >> simp[] >> Cases_on `h` >> fs[in_traj_cross])
    >- (rename [`traj_cross (tcons hs hws has hss hrs) = traj_cross (tcons gs gws gas gss grs)`] >>
        fs[EXTENSION] >> last_x_assum $ irule_at Any >> rename [`h ∈ _`] >>
        first_assum $ drule_then assume_tac o iffRL >> Cases_on `h` >- fs[in_traj_cross] >>
        rename [`tcons h w a s r`] >> fs[in_traj_cross] >> qexists_tac `h` >> simp[] >>
        rpt CONJ_TAC >> qx_gen_tac `v`
        >| let fun fv tm = first_x_assum $ qspec_then tm assume_tac in [fv `tcons v w a s r`,
            fv `tcons h v a s r`,fv `tcons h w v s r`,fv `tcons h w a v r`,fv `tcons h w a s v`] end >>
        rfs[in_traj_cross])
QED

Definition traj_m_space_def:
    traj_m_space (m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space) =
        BIGUNION (IMAGE traj_cross (traj_inf_gen (m_space m_s) (m_space m_o) (m_space m_a) (m_space m_r)))
End

Theorem in_traj_m_space:
    (∀m_s m_o m_a m_r s. ((init s): (α,ρ,σ,ω) traj) ∈ traj_m_space m_s m_o m_a m_r ⇔ s ∈ m_space m_s) ∧
    (∀m_s m_o m_a m_r (h: (α,ρ,σ,ω) traj) w a s r. (tcons h w a s r) ∈ traj_m_space m_s m_o m_a m_r ⇔
        w ∈ m_space m_o ∧ a ∈ m_space m_a ∧ s ∈ m_space m_s ∧ r ∈ m_space m_r ∧ h ∈ traj_m_space m_s m_o m_a m_r)
Proof
    simp[GSYM FORALL_AND_THM,RIGHT_AND_FORALL_THM] >> rpt gen_tac >>
    `∀(h: (α,ρ,σ,ω) traj) m_s m_o m_a m_r. h ∈ traj_m_space m_s m_o m_a m_r ⇔
        traj_m_space m_s m_o m_a m_r h` by simp[IN_APP] >>
    simp[traj_m_space_def] >> pop_assum kall_tac >> CONJ_TAC >> eq_tac >> DISCH_TAC
    >- (gvs[] >> Cases_on `x` >> fs[in_traj_cross] >> gvs[in_traj_inf_gen])
    >- (qexists_tac `traj_cross (init (m_space m_s))` >> simp[in_traj_cross] >>
        qexists_tac `init (m_space m_s)` >> simp[in_traj_inf_gen])
    >- (gvs[] >> Cases_on `x` >> fs[in_traj_cross] >> gvs[in_traj_inf_gen] >> rename [`h ∈ traj_cross hs`] >>
        qexists_tac `traj_cross hs` >> simp[] >> qexists_tac `hs` >> simp[])
    >- (gvs[] >> rename [`h ∈ traj_cross hs`] >>
        qexists_tac `traj_cross (tcons hs (m_space m_o) (m_space m_a) (m_space m_s) (m_space m_r))` >>
        simp[in_traj_cross] >> qexists_tac `tcons hs (m_space m_o) (m_space m_a) (m_space m_s) (m_space m_r)` >>
        simp[in_traj_inf_gen])
QED

Definition traj_m_space_n_def:
    traj_m_space_n n (m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space) =
        traj_cross (traj_n_gen n (m_space m_s) (m_space m_o) (m_space m_a) (m_space m_r))
End

Theorem in_traj_m_space_n:
    (∀m_s m_o m_a m_r s.
        ((init s): (α,ρ,σ,ω) traj) ∈ traj_m_space_n 0 m_s m_o m_a m_r ⇔ s ∈ m_space m_s) ∧
    (∀n m_s m_o m_a m_r s.
        ((init s): (α,ρ,σ,ω) traj) ∉ traj_m_space_n (SUC n) m_s m_o m_a m_r) ∧
    (∀m_s m_o m_a m_r (h: (α,ρ,σ,ω) traj) w a s r.
        (tcons h w a s r) ∉ traj_m_space_n 0 m_s m_o m_a m_r) ∧
    (∀n m_s m_o m_a m_r (h: (α,ρ,σ,ω) traj) w a s r.
        (tcons h w a s r) ∈ traj_m_space_n (SUC n) m_s m_o m_a m_r ⇔
        w ∈ m_space m_o ∧ a ∈ m_space m_a ∧ s ∈ m_space m_s ∧ r ∈ m_space m_r ∧
        h ∈ traj_m_space_n n m_s m_o m_a m_r)
Proof
    simp[GSYM FORALL_AND_THM,RIGHT_AND_FORALL_THM] >> rpt gen_tac >>
    `∀(h: (α,ρ,σ,ω) traj) n m_s m_o m_a m_r. h ∈ traj_m_space_n n m_s m_o m_a m_r ⇔
        traj_m_space_n n m_s m_o m_a m_r h` by simp[IN_APP] >>
    simp[traj_m_space_n_def] >> pop_assum kall_tac >> rpt CONJ_TAC >> TRY (eq_tac >> DISCH_TAC) >>
    fs[traj_n_gen_def,traj_cross_def]
QED

Theorem traj_m_space_n_subset_traj_m_space:
    ∀n (m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space).
        traj_m_space_n n m_s m_o m_a m_r ⊆ traj_m_space m_s m_o m_a m_r
Proof
    simp[SUBSET_DEF] >> rpt gen_tac >> rename [`h ∈ _`] >> qid_spec_tac `h` >>
    Induct_on `n` >> rw[] >> rename [`h ∈ _`] >> Cases_on `h` >> fs[in_traj_m_space_n,in_traj_m_space]
QED

Theorem traj_m_space_alt:
    ∀(m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space).
        traj_m_space m_s m_o m_a m_r = BIGUNION (IMAGE (λn. traj_m_space_n n m_s m_o m_a m_r) UNIV)
Proof
    rw[EXTENSION,IN_BIGUNION_IMAGE] >> rename [`h ∈ _`] >> REVERSE eq_tac >> rw[]
    >- simp[SIMP_RULE (srw_ss ()) [SUBSET_DEF] traj_m_space_n_subset_traj_m_space,SF SFY_ss] >>
    pop_assum mp_tac >> Induct_on `h` >> rw[]
    >- (qexists_tac `0` >> fs[in_traj_m_space,in_traj_m_space_n]) >>
    fs[in_traj_m_space] >> qexists_tac `SUC n` >> simp[in_traj_m_space_n]
QED

Definition traj_rect_sets_def:
    traj_rect_sets (m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space) =
        IMAGE traj_cross (BIGUNION (IMAGE traj_cross (traj_inf_gen
            (measurable_sets m_s) (measurable_sets m_o) (measurable_sets m_a) (measurable_sets m_r))))
End

Definition traj_rect_sets_n_def:
    traj_rect_sets_n n (m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space) =
        IMAGE traj_cross (traj_cross (traj_n_gen n
            (measurable_sets m_s) (measurable_sets m_o) (measurable_sets m_a) (measurable_sets m_r)))
End

Theorem traj_rect_sets_alt:
    ∀(m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space).
        traj_rect_sets m_s m_o m_a m_r = BIGUNION (IMAGE (λn. traj_rect_sets_n n m_s m_o m_a m_r) UNIV)
Proof
    simp[traj_rect_sets_def,traj_rect_sets_n_def,traj_inf_gen_alt,IMAGE_BIGUNION,IMAGE_IMAGE,o_DEF]
QED

Theorem in_traj_rect_sets_n:
    (∀(m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space) hs.
        hs ∈ traj_rect_sets_n 0 m_s m_o m_a m_r ⇔ ∃ss. hs = traj_cross (init ss) ∧ ss ∈ measurable_sets m_s) ∧
    (∀n (m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space) gs.
        gs ∈ traj_rect_sets_n (SUC n) m_s m_o m_a m_r ⇔
        ∃hs ws as ss rs. gs = traj_cross (tcons hs ws as ss rs) ∧
        ws ∈ measurable_sets m_o ∧ as ∈ measurable_sets m_a ∧ ss ∈ measurable_sets m_s ∧
        rs ∈ measurable_sets m_r ∧ traj_cross hs ∈ traj_rect_sets_n n m_s m_o m_a m_r)
Proof
    CONJ_ASM1_TAC
    >- (rw[traj_rect_sets_n_def] >> eq_tac >> DISCH_TAC
        >- (gvs[traj_n_gen_def] >> rename [`h ∈ _`] >> Cases_on `h` >>
            fs[in_traj_cross] >> rename [`ss ∈ _`] >> qexists_tac `ss` >> simp[])
        >- (gvs[] >> qexists_tac `init ss` >> simp[traj_n_gen_def,in_traj_cross])) >>
    Induct_on `n` >| [all_tac,pop_assum $ assume_tac o GSYM] >>
    rw[] >> gvs[traj_rect_sets_n_def] >> eq_tac >> DISCH_TAC
    >- (gvs[] >> rename [`h ∈ _`] >> Cases_on `h` >>
        FULL_SIMP_TAC pure_ss [ONE,traj_n_gen_def,in_traj_cross] >> rename [`tcons hs ws as ss rs`] >>
        qexistsl_tac [`hs`,`ws`,`as`,`ss`,`rs`] >> simp[] >> last_x_assum $ irule o iffLR >>
        qexists_tac `hs` >> simp[])
    >- (gvs[] >> rename [`traj_cross hs = traj_cross (init ts)`] >> fs[traj_n_gen_def] >>
        last_x_assum $ qspecl_then [`m_s`,`ts`] assume_tac o
            SIMP_RULE (srw_ss ()) [GSYM LEFT_FORALL_IMP_THM] o iffRL >> rfs[] >>
        fs[] >> qexists_tac `tcons x ws as ss rs` >> ASM_SIMP_TAC bool_ss [ONE,traj_n_gen_def,in_traj_cross] >>
        pop_assum kall_tac >> gvs[traj_cross_eq,in_traj_cross] >> simp[traj_cross_empty])
    >- (last_x_assum kall_tac >> gvs[] >> rename [`h ∈ _`] >> pop_assum mp_tac >> Cases_on `h` >>
        simp[Once traj_n_gen_def,in_traj_cross] >> rw[] >> rename [`tcons hs ws as ss rs`] >>
        qexistsl_tac [`hs`,`ws`,`as`,`ss`,`rs`] >> simp[] >> qexists_tac `hs` >> simp[])
    >- (last_x_assum kall_tac >> pop_assum mp_tac >> simp[Once traj_n_gen_def] >> DISCH_TAC >>
        gvs[] >> rename [`traj_cross hs = traj_cross fs`] >> Cases_on `fs` >> fs[in_traj_cross] >>
        rename [`_ = traj_cross (tcons hsh hsw hsa hss hsr)`] >>
        last_x_assum $ qspecl_then [`m_s`,`m_o`,`m_a`,`m_r`,`hsh`,`hsw`,`hsa`,`hss`,`hsr`,`hsh`]
            assume_tac o SIMP_RULE (srw_ss ()) [GSYM LEFT_FORALL_IMP_THM,GSYM RIGHT_EXISTS_AND_THM] o iffLR >>
        rfs[] >> rename [`traj_cross (tcons _ _ _ _ _) = traj_cross gs`] >> fs[] >>
        qexists_tac `tcons gs ws as ss rs` >> simp[Once traj_n_gen_def,in_traj_cross] >>
        pop_assum kall_tac >> gvs[traj_cross_eq,in_traj_cross] >> simp[traj_cross_empty])
QED

Definition traj_measurable_sets_def:
    traj_measurable_sets (m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space) =
        subsets (sigma (traj_m_space m_s m_o m_a m_r) (traj_rect_sets m_s m_o m_a m_r))
End

Definition traj_measurable_sets_n_def:
    traj_measurable_sets_n n (m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space) =
        subsets (sigma (traj_m_space_n n m_s m_o m_a m_r) (traj_rect_sets_n n m_s m_o m_a m_r))
End

Theorem traj_rect_set_n_measurable:
    ∀n (m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space).
        traj_rect_sets_n n m_s m_o m_a m_r ⊆ traj_measurable_sets_n n m_s m_o m_a m_r
Proof
    simp[traj_measurable_sets_n_def,SIGMA_SUBSET_SUBSETS]
QED

Theorem subset_class_traj_rect_sets_n:
    ∀n (m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space).
        subset_class (m_space m_s) (measurable_sets m_s) ∧ subset_class (m_space m_o) (measurable_sets m_o) ∧
        subset_class (m_space m_a) (measurable_sets m_a) ∧ subset_class (m_space m_r) (measurable_sets m_r) ⇒
        subset_class (traj_m_space_n n m_s m_o m_a m_r) (traj_rect_sets_n n m_s m_o m_a m_r)
Proof
    rw[] >> Induct_on `n` >> fs[subset_class_def] >> simp[in_traj_rect_sets_n] >> rw[] >>
    rpt $ first_x_assum $ dxrule_then assume_tac >> simp[SUBSET_DEF] >> qx_gen_tac `h` >>
    Cases_on `h` >> simp[in_traj_cross,in_traj_m_space_n] >> fs[SUBSET_DEF]
QED

Theorem traj_m_space_n_rect_set:
    ∀n (m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space).
        measure_space m_s ∧ measure_space m_o ∧ measure_space m_a ∧ measure_space m_r ⇒
        traj_m_space_n n m_s m_o m_a m_r ∈ traj_rect_sets_n n m_s m_o m_a m_r
Proof
    rw[] >> Induct_on `n` >> fs[in_traj_rect_sets_n,traj_m_space_n_def,traj_n_gen_def]
    >- (qexists_tac `m_space m_s` >> simp[MEASURE_SPACE_SPACE])
    >- (qexistsl_tac [`traj_n_gen n (m_space m_s) (m_space m_o) (m_space m_a) (m_space m_r)`,
            `m_space m_o`,`m_space m_a`,`m_space m_s`,`m_space m_r`] >>
        simp[MEASURE_SPACE_SPACE])
QED

Definition step_cross_def:
    (step_cross hs ws as ss rs (init s) ⇔ F) ∧
    (step_cross hs ws as ss rs (tcons (h: (α,ρ,σ,ω) traj) w a s r) ⇔
        w ∈ ws ∧ a ∈ as ∧ s ∈ ss ∧ r ∈ rs ∧ h ∈ hs)
End

Theorem in_step_cross:
    (∀hs ws as ss rs s. (init s):((α,ρ,σ,ω) traj) ∉ step_cross hs ws as ss rs) ∧
    (∀hs ws as ss rs (h: (α,ρ,σ,ω) traj) w a s r. tcons h w a s r ∈ step_cross hs ws as ss rs ⇔
        w ∈ ws ∧ a ∈ as ∧ s ∈ ss ∧ r ∈ rs ∧ h ∈ hs)
Proof
    simp[GSYM FORALL_AND_THM,RIGHT_AND_FORALL_THM] >> rpt gen_tac >> simp[IN_APP,step_cross_def]
QED

Definition step_rect_sets_n_def:
    step_rect_sets_n 0 (m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space) =
        IMAGE traj_cross (traj_cross (init (measurable_sets m_s))) ∧
    step_rect_sets_n (SUC n) (m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space) =
        {step_cross hs ws as ss rs | hs ∈ traj_measurable_sets_n n m_s m_o m_a m_r ∧
        ws ∈ measurable_sets m_o ∧ as ∈ measurable_sets m_a ∧ ss ∈ measurable_sets m_s ∧ rs ∈ measurable_sets m_r}
End

Theorem in_step_rect_sets_n:
    (∀(m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space) hs.
        hs ∈ step_rect_sets_n 0 m_s m_o m_a m_r ⇔ ∃ss. hs = traj_cross (init ss) ∧ ss ∈ measurable_sets m_s) ∧
    (∀n (m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space) gs.
        gs ∈ step_rect_sets_n (SUC n) m_s m_o m_a m_r ⇔
        ∃hs ws as ss rs. gs = step_cross hs ws as ss rs ∧
        hs ∈ traj_measurable_sets_n n m_s m_o m_a m_r ∧ ws ∈ measurable_sets m_o ∧
        as ∈ measurable_sets m_a ∧ ss ∈ measurable_sets m_s ∧ rs ∈ measurable_sets m_r)
Proof
    rw[] >> simp[step_rect_sets_n_def] >> eq_tac >> rw[]
    >- (rename [`hr ∈ _`] >> Cases_on `hr` >> fs[in_traj_cross] >> rename [`ss ∈ _`] >>
        qexists_tac `ss` >> simp[])
    >- (qexists_tac `init ss` >> simp[in_traj_cross])
QED

Theorem traj_rect_sets_n_subset_step_rect_sets_n:
    ∀n (m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space).
        traj_rect_sets_n n m_s m_o m_a m_r ⊆ step_rect_sets_n n m_s m_o m_a m_r
Proof
    rw[] >> simp[SUBSET_DEF] >> Induct_on `n` >>
    simp[traj_rect_sets_n_def,traj_n_gen_def,step_rect_sets_n_def] >> qx_gen_tac `h` >> rw[] >>
    rename [`h ∈ _`] >> Cases_on `h` >> fs[in_traj_cross] >> rename [`tcons hs ws as ss rs`] >>
    qexistsl_tac [`traj_cross hs`,`ws`,`as`,`ss`,`rs`] >> simp[] >>
    irule_at Any $ SIMP_RULE (srw_ss ()) [SUBSET_DEF] traj_rect_set_n_measurable >>
    simp[traj_rect_sets_n_def,EXTENSION] >> qx_gen_tac `h` >>
    Cases_on `h` >> simp[in_traj_cross,in_step_cross]
QED

Theorem traj_cross_step_cross:
    ∀hs ws as ss rs. traj_cross (tcons hs ws as ss rs): (α,ρ,σ,ω) traj -> bool =
        step_cross (traj_cross hs) ws as ss rs
Proof
    rw[] >> simp[EXTENSION] >> qx_gen_tac `h` >> Cases_on `h` >>
    simp[in_traj_cross,in_step_cross]
QED

Theorem step_rect_set_n_measurable:
    ∀n (m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space).
        measure_space m_s ∧ measure_space m_o ∧ measure_space m_a ∧ measure_space m_r ⇒
        step_rect_sets_n n m_s m_o m_a m_r ⊆ traj_measurable_sets_n n m_s m_o m_a m_r
Proof
    rw[] >> simp[SUBSET_DEF] >> Cases_on `n` >> qx_gen_tac `hs` >> rw[step_rect_sets_n_def]
    >- (irule $ SIMP_RULE (srw_ss ()) [SUBSET_DEF] traj_rect_set_n_measurable >>
        simp[traj_rect_sets_n_def,traj_n_gen_def]) >>
    rename [`SUC n`,`step_cross hs _ _ _ _ ∈ _`] >> fs[traj_measurable_sets_n_def,sigma_def] >> rw[] >>
    Cases_on `ws = ∅ ∨ as = ∅ ∨ ss = ∅ ∨ rs = ∅`
    >- (`∅ ∈ P` by fs[sigma_algebra_def,algebra_def] >>
        `step_cross hs ws as ss rs = ∅` suffices_by simp[] >>
        simp[EXTENSION] >> qx_gen_tac `h` >> Cases_on `h` >> simp[in_step_cross] >> fs[]) >>
    last_x_assum $ qspec_then `{hs| step_cross hs ws as ss rs ∈ P}` $
        irule o SIMP_RULE (srw_ss ()) [] >>
    REVERSE CONJ_TAC
    >- (simp[SUBSET_DEF] >> qx_gen_tac `hs` >> strip_tac >>
        qpat_x_assum `_ ⊆ _` $ irule_at Any o SIMP_RULE (srw_ss ()) [SUBSET_DEF] >>
        simp[in_traj_rect_sets_n] >> gvs[traj_rect_sets_n_def] >> rename [`hs ∈ _`] >>
        qexistsl_tac [`hs`,`ws`,`as`,`ss`,`rs`] >> simp[traj_cross_step_cross] >>
        qexists_tac `hs` >> simp[]) >>
    rw[SIGMA_ALGEBRA_ALT_DIFF]
    >- (fs[GSYM MEMBER_NOT_EMPTY] >>
        rename [`{hs | step_cross hs ws as ss rs ∈ P}`,`w ∈ ws`,`a ∈ as`,`s ∈ ss`,`r ∈ rs`] >>
        dxrule_then assume_tac SIGMA_ALGEBRA_SUBSET_CLASS >> fs[subset_class_def] >> rw[] >>
        first_x_assum $ dxrule_then mp_tac >> rename [`step_cross hs _ _ _ _`] >> simp[SUBSET_DEF] >>
        rw[] >> rename [`h ∈ _`] >> first_x_assum $ qspec_then `tcons h w a s r` mp_tac >>
        simp[in_step_cross,in_traj_m_space_n])
    (* this is the problem case *)
    >- (qpat_x_assum `_ ⊆ _` $ irule_at Any o SIMP_RULE (srw_ss ()) [SUBSET_DEF] >>
        simp[in_traj_rect_sets_n,traj_m_space_n_def] >>
        qexistsl_tac [`traj_n_gen n (m_space m_s) (m_space m_o) (m_space m_a) (m_space m_r)`,
            `ws`,`as`,`ss`,`rs`] >>
        simp[traj_cross_step_cross] >> simp[GSYM traj_m_space_n_def,traj_m_space_n_rect_set])
    >- (dxrule_then mp_tac SIGMA_ALGEBRA_DIFF >> simp[] >>
        DISCH_THEN $ qspecl_then [`step_cross t ws as ss rs`,`step_cross s ws as ss rs`] mp_tac >>
        simp[] >> qmatch_abbrev_tac `hs1 ∈ _ ⇒ hs2 ∈ _` >> `hs1 = hs2` suffices_by simp[] >>
        UNABBREV_ALL_TAC >> simp[EXTENSION] >> qx_gen_tac `h` >> Cases_on `h` >> simp[in_step_cross] >>
        eq_tac >> strip_tac >> simp[])
    >- (dxrule_then mp_tac SIGMA_ALGEBRA_COUNTABLE_UNION >> simp[] >>
        DISCH_THEN $ qspec_then `IMAGE (λhs. step_cross hs ws as ss rs) c` mp_tac >>
        `BIGUNION (IMAGE (λhs. step_cross hs ws as ss rs) c) = step_cross (BIGUNION c) ws as ss rs` suffices_by (
            DISCH_THEN SUBST1_TAC >> DISCH_THEN irule >> simp[image_countable] >>
            fs[SUBSET_DEF] >> rw[] >> fs[]) >>
        simp[EXTENSION,IN_BIGUNION_IMAGE] >> qx_gen_tac `h` >> Cases_on `h` >> simp[in_step_cross] >>
        eq_tac >> strip_tac >> simp[SF SFY_ss])
QED

Theorem traj_measurable_sets_n_alt:
    ∀n (m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space).
        measure_space m_s ∧ measure_space m_o ∧ measure_space m_a ∧ measure_space m_r ⇒
        traj_measurable_sets_n n m_s m_o m_a m_r =
        subsets (sigma (traj_m_space_n n m_s m_o m_a m_r) (step_rect_sets_n n m_s m_o m_a m_r))
Proof
    rw[traj_measurable_sets_n_def] >> irule SUBSET_ANTISYM >> CONJ_TAC
    >- (irule SIGMA_MONOTONE >> simp[traj_rect_sets_n_subset_step_rect_sets_n])
    >- (irule SIGMA_BOUNDED >> simp[GSYM traj_measurable_sets_n_def] >>
        simp[step_rect_set_n_measurable])
QED

Definition traj_sig_alg_def:
    traj_sig_alg (m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space) =
        (traj_m_space m_s m_o m_a m_r,traj_measurable_sets m_s m_o m_a m_r)
End

Definition traj_sig_alg_n_def:
    traj_sig_alg_n n (m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space) =
        (traj_m_space_n n m_s m_o m_a m_r,traj_measurable_sets_n n m_s m_o m_a m_r)
End

Theorem sigma_algebra_traj_sig_alg:
    ∀(m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space).
        measure_space m_s ∧ measure_space m_o ∧ measure_space m_a ∧ measure_space m_r ⇒
        sigma_algebra (traj_sig_alg m_s m_o m_a m_r)
Proof
    rw[traj_sig_alg_def,traj_measurable_sets_def] >> simp[SIGMA_REDUCE] >>
    irule SIGMA_ALGEBRA_SIGMA >> simp[subset_class_def] >>
    simp[traj_rect_sets_alt,IN_BIGUNION_IMAGE,GSYM LEFT_FORALL_IMP_THM] >>
    Induct_on `n` >> rw[in_traj_rect_sets_n] >> simp[SUBSET_DEF] >> qx_gen_tac `h` >>
    Cases_on `h` >> simp[in_traj_cross,in_traj_m_space,MEASURE_SPACE_IN_MSPACE,SF SFY_ss] >>
    last_x_assum $ dxrule_then assume_tac >> fs[SUBSET_DEF]
QED

Theorem sigma_algebra_traj_sig_alg_n:
    ∀n (m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space).
        measure_space m_s ∧ measure_space m_o ∧ measure_space m_a ∧ measure_space m_r ⇒
        sigma_algebra (traj_sig_alg_n n m_s m_o m_a m_r)
Proof
    rw[traj_sig_alg_n_def,traj_measurable_sets_n_def] >> simp[SIGMA_REDUCE] >>
    irule SIGMA_ALGEBRA_SIGMA >> simp[subset_class_def] >> qid_spec_tac `n` >>
    Induct_on `n` >> rw[in_traj_rect_sets_n] >> simp[SUBSET_DEF] >> qx_gen_tac `h` >>
    Cases_on `h` >> simp[in_traj_cross,in_traj_m_space_n,MEASURE_SPACE_IN_MSPACE,SF SFY_ss] >>
    last_x_assum $ dxrule_then assume_tac >> fs[SUBSET_DEF]
QED

Definition traj_measure_rec_lex_def:
    traj_measure_rec_lex (INL (n,_)) = (n,0) ∧
    traj_measure_rec_lex (INR (n,_)) = (n,SUC 0)
End

Definition traj_measure_rec_def:
    traj_measure_n 0 (m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space) = (λhs.
        ∫⁺ m_s (λs. 𝟙 hs (init s))) ∧
    traj_measure_n (SUC n) (m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space) = (λhs.
        ∫⁺ (traj_measure_space_n n m_s m_o m_a m_r)
        (λh. ∫⁺ m_o (λw. ∫⁺ m_a (λa. ∫⁺ m_s (λs. ∫⁺ m_r (λr. 𝟙 hs (tcons h w a s r))))))) ∧
    traj_measure_space_n n (m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space) =
        (traj_m_space_n n m_s m_o m_a m_r,traj_measurable_sets_n n m_s m_o m_a m_r,traj_measure_n n m_s m_o m_a m_r)
Termination
    WF_REL_TAC `inv_image ($< LEX $<) traj_measure_rec_lex` >> simp[traj_measure_rec_lex_def]
End

Theorem traj_measure_n_def:
    (∀(m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space).
        traj_measure_n 0 m_s m_o m_a m_r = (λhs. ∫⁺ m_s (λs. 𝟙 hs (init s)))) ∧
    (∀n (m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space).
        traj_measure_n (SUC n) m_s m_o m_a m_r = (λhs. ∫⁺ (traj_measure_space_n n m_s m_o m_a m_r)
        (λh. ∫⁺ m_o (λw. ∫⁺ m_a (λa. ∫⁺ m_s (λs. ∫⁺ m_r (λr. 𝟙 hs (tcons h w a s r))))))))
Proof
    simp[traj_measure_rec_def]
QED

Definition traj_measure_def:
    traj_measure (m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space) =
        (λhs. suminf (λn. traj_measure_n n m_s m_o m_a m_r hs))
End

Definition traj_measure_space_def:
    traj_measure_space (m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space) =
        (traj_m_space m_s m_o m_a m_r,traj_measurable_sets m_s m_o m_a m_r,traj_measure m_s m_o m_a m_r)
End

Theorem traj_measure_space_n_def:
    ∀n (m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space).
        traj_measure_space_n n m_s m_o m_a m_r =
        (traj_m_space_n n m_s m_o m_a m_r,traj_measurable_sets_n n m_s m_o m_a m_r,traj_measure_n n m_s m_o m_a m_r)
Proof
    simp[traj_measure_rec_def]
QED

Theorem m_space_traj_measure_space:
    (∀(m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space).
        m_space (traj_measure_space m_s m_o m_a m_r) = traj_m_space m_s m_o m_a m_r) ∧
    (∀n (m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space).
        m_space (traj_measure_space_n n m_s m_o m_a m_r) = traj_m_space_n n m_s m_o m_a m_r)
Proof
    simp[traj_measure_space_def,traj_measure_space_n_def]
QED

Theorem measurable_sets_traj_measure_space:
    (∀(m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space).
        measurable_sets (traj_measure_space m_s m_o m_a m_r) = traj_measurable_sets m_s m_o m_a m_r) ∧
    (∀n (m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space).
        measurable_sets (traj_measure_space_n n m_s m_o m_a m_r) = traj_measurable_sets_n n m_s m_o m_a m_r)
Proof
    simp[traj_measure_space_def,traj_measure_space_n_def]
QED

Theorem measure_traj_measure_space:
    (∀(m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space).
        measure (traj_measure_space m_s m_o m_a m_r) = traj_measure m_s m_o m_a m_r) ∧
    (∀n (m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space).
        measure (traj_measure_space_n n m_s m_o m_a m_r) = traj_measure_n n m_s m_o m_a m_r)
Proof
    simp[traj_measure_space_def,traj_measure_space_n_def]
QED

Theorem sig_alg_traj_measure_space:
    (∀(m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space).
        sig_alg (traj_measure_space m_s m_o m_a m_r) = traj_sig_alg m_s m_o m_a m_r) ∧
    (∀n (m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space).
        sig_alg (traj_measure_space_n n m_s m_o m_a m_r) = traj_sig_alg_n n m_s m_o m_a m_r)
Proof
    simp[traj_measure_space_def,traj_measure_space_n_def,traj_sig_alg_def,traj_sig_alg_n_def]
QED

Theorem space_traj_sig_alg:
    (∀(m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space).
        space (traj_sig_alg m_s m_o m_a m_r) = traj_m_space m_s m_o m_a m_r) ∧
    (∀n (m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space).
        space (traj_sig_alg_n n m_s m_o m_a m_r) = traj_m_space_n n m_s m_o m_a m_r)
Proof
    simp[traj_sig_alg_def,traj_sig_alg_n_def]
QED

Theorem subsets_traj_sig_alg:
    (∀(m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space).
        subsets (traj_sig_alg m_s m_o m_a m_r) = traj_measurable_sets m_s m_o m_a m_r) ∧
    (∀n (m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space).
        subsets (traj_sig_alg_n n m_s m_o m_a m_r) = traj_measurable_sets_n n m_s m_o m_a m_r)
Proof
    simp[traj_sig_alg_def,traj_sig_alg_n_def]
QED

val TRAJ_ss = named_rewrites_with_names "TRAJ" $ map name_to_thname [
    "m_space_traj_measure_space","measurable_sets_traj_measure_space","measure_traj_measure_space",
    "sig_alg_traj_measure_space","space_traj_sig_alg","subsets_traj_sig_alg"];

val _ = augment_srw_ss [TRAJ_ss];

(* may be able to work with only subset_class req *)
Theorem subset_class_step_rect_sets_n:
    ∀n (m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space).
        measure_space m_s ∧ measure_space m_o ∧ measure_space m_a ∧ measure_space m_r ⇒
        subset_class (traj_m_space_n n m_s m_o m_a m_r) (step_rect_sets_n n m_s m_o m_a m_r)
Proof
    rw[] >> `sigma_algebra (traj_sig_alg_n n m_s m_o m_a m_r)` by simp[sigma_algebra_traj_sig_alg_n] >>
    `step_rect_sets_n n m_s m_o m_a m_r ⊆ traj_measurable_sets_n n m_s m_o m_a m_r` by
        simp[step_rect_set_n_measurable] >>
    dxrule_then mp_tac SIGMA_ALGEBRA_SUBSET_CLASS >> fs[SUBSET_DEF] >> simp[subset_class_def]
QED

Theorem in_measure_preserving_init:
    ∀(m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space).
        measure_space m_s ∧ measure_space m_o ∧ measure_space m_a ∧ measure_space m_r ⇒
        init ∈ measure_preserving m_s (traj_measure_space_n 0 m_s m_o m_a m_r)
Proof
    rw[] >>
    `BIJ init (m_space m_s) (traj_m_space_n 0 m_s m_o m_a m_r)` by (
        rw[BIJ_ALT,EXISTS_UNIQUE_ALT,FUNSET,traj_m_space_n_def,traj_n_gen_def]
        >- (rename [`init s ∈ _`] >> simp[in_traj_cross])
        >- (rename [`h ∈ _`] >> Cases_on `h` >> fs[in_traj_cross] >>
            qexists_tac `s` >> rw[] >> eq_tac >> rw[] >> simp[])) >>
    `∀ss. (traj_cross (init ss)): (α,ρ,σ,ω) traj -> bool = IMAGE init ss` by (rw[] >>
        simp[EXTENSION,in_traj_cross] >> qx_gen_tac `h` >> Cases_on `h` >> simp[in_traj_cross]) >>
    rw[in_measure_preserving,in_measurability_preserving_alt,sigma_algebra_traj_sig_alg_n]
    >| [qexistsl_tac [`measurable_sets m_s`,`traj_rect_sets_n 0 m_s m_o m_a m_r`] >> rw[],all_tac]
    >- simp[MEASURE_SPACE_SIGMA_STABLE]
    >- simp[traj_sig_alg_n_def,traj_measurable_sets_n_def,SIGMA_REDUCE]
    >- simp[MEASURE_SPACE_SUBSET_CLASS]
    >- simp[MEASURE_SPACE_SUBSET_CLASS,subset_class_traj_rect_sets_n]
    >- (rename [`_ _ ss ∈ _`] >> simp[in_traj_rect_sets_n] >> qexists_tac `ss` >> simp[])
    >- (gvs[in_traj_rect_sets_n] >> drule_all_then assume_tac MEASURABLE_SETS_SUBSET_SPACE >>
        drule_all_then SUBST1_TAC BIJ_PREIMAGE_IMAGE >> simp[])
    >- (rename [`_ _ ss = _`] >> simp[traj_measure_n_def] >>
        drule_all_then (SUBST1_TAC o SYM) pos_fn_integral_indicator >> irule pos_fn_integral_cong >>
        simp[INDICATOR_FN_POS] >> qx_gen_tac `s` >> rw[indicator_fn_def])
QED

Theorem in_measure_preserving_tcons:
    ∀n (m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space).
        sigma_finite_measure_space m_s ∧ sigma_finite_measure_space m_o ∧
        sigma_finite_measure_space m_a ∧ sigma_finite_measure_space m_r ∧
        sigma_finite_measure_space (traj_measure_space_n n m_s m_o m_a m_r) ⇒
        (λ(h,w,a,s,r). tcons h w a s r) ∈ measure_preserving
        (traj_measure_space_n n m_s m_o m_a m_r × m_o × m_a × m_s × m_r)
        (traj_measure_space_n (SUC n) m_s m_o m_a m_r)
Proof
    rw[] >> REVERSE $ rw[in_measure_preserving]
    >- (rename [`hs ∈ _`] >> qmatch_abbrev_tac `_ (m_h × _ × _ × _ × _) _ = _` >> simp[traj_measure_n_def] >>
        `sigma_finite_measure_space (m_s × m_r) ∧ sigma_finite_measure_space (m_a × m_s × m_r) ∧
          sigma_finite_measure_space (m_o × m_a × m_s × m_r)` by simp[sigma_finite_measure_space_prod_measure] >>
        map_every (fn tm => drule_all_then mp_tac measure_prod_measure_space_itr >>
            qpat_x_assum `_ ∈ _` kall_tac >> simp[] >> DISCH_TAC >> irule IRULER >> simp[FUN_EQ_THM] >>
            qx_gen_tac tm >> pop_assum $ qspec_then tm assume_tac o cj 2) [`h`,`w`,`a`,`s`] >>
        simp[GSYM pos_fn_integral_indicator] >> irule IRULER >>
        simp[FUN_EQ_THM] >> qx_gen_tac `r` >> simp[indicator_fn_def,EXISTS_PROD]) >>
    pop_assum kall_tac >> fs[sigma_finite_measure_space_def] >> NTAC 4 $ qpat_x_assum `sigma_finite _` kall_tac >>
    `BIJ (λ(h,w,a,s,r). tcons h w a s r) (m_space (traj_measure_space_n n m_s m_o m_a m_r × m_o × m_a × m_s × m_r))
      (traj_m_space_n (SUC n) m_s m_o m_a m_r)` by (
        simp[m_space_prod_measure_space,traj_m_space_n_def,traj_n_gen_def] >>
        simp[BIJ_ALT,EXISTS_UNIQUE_ALT,EXISTS_PROD,FORALL_PROD,FUNSET,in_traj_cross] >>
        qx_gen_tac `h` >> Cases_on `h` >> simp[in_traj_cross] >>
        rename [`w ∈ _ ∧ a ∈ _ ∧ s ∈ _ ∧ r ∈ _ ∧ h ∈ _`] >> rw[] >> qexistsl_tac [`h`,`w`,`a`,`s`,`r`] >>
        rw[] >> eq_tac >> rw[] >> simp[]) >>
    `∀hs ws as ss rs. (step_cross hs ws as ss rs): (α,ρ,σ,ω) traj -> bool = 
      IMAGE (λ(h,w,a,s,r). tcons h w a s r) (hs × ws × as × ss × rs)` by (rw[] >>
        simp[EXTENSION,EXISTS_PROD] >> qx_gen_tac `h` >> Cases_on `h` >> simp[in_step_cross] >>
        (* redifinition of step_cross? *)
        eq_tac >> strip_tac >> simp[]) >>
    simp[in_measurability_preserving_alt,sigma_algebra_traj_sig_alg_n] >>
    qexistsl_tac [`prod_sets (traj_measurable_sets_n n m_s m_o m_a m_r) (prod_sets (measurable_sets m_o)
        (prod_sets (measurable_sets m_a) (prod_sets (measurable_sets m_s) (measurable_sets m_r))))`,
        `step_rect_sets_n (SUC n) m_s m_o m_a m_r`] >> rw[]
    >- (NTAC 2 $ pop_assum kall_tac >>
        `sigma_algebra (traj_sig_alg_n n m_s m_o m_a m_r)` by simp[sigma_algebra_traj_sig_alg_n] >>
        map_every imp_res_tac
            [MEASURE_SPACE_SPACE,SIGMA_ALGEBRA_SPACE,MEASURE_SPACE_SUBSET_CLASS,SIGMA_ALGEBRA_SUBSET_CLASS] >>
        NTAC 5 $ last_x_assum kall_tac >> fs[] >> simp[m_space_prod_measure_space,sig_alg_prod_measure_space] >>
        qspecl_then [`sig_alg m_s`,`sig_alg m_r`] SUBST1_TAC prod_sigma_def >> simp[] >>
        map_every (fn tms => qspecl_then tms mp_tac SIGMA_PROD_ITR >> simp[Excl "IN_PROD_SETS"] >>
                strip_tac >> pop_assum kall_tac >> rename [`subset_class sp sts`]) [
            [`sig_alg m_a`,`sig_alg m_s`,`sig_alg m_r`],[`sig_alg m_o`,`sig_alg m_a`,`sp,sts`],
            [`traj_sig_alg_n n m_s m_o m_a m_r`,`sig_alg m_o`,`sp,sts`]])
    >- simp[traj_sig_alg_n_def,traj_measurable_sets_n_alt,SIGMA_REDUCE]
    >- (simp[m_space_prod_measure_space,prod_sets_def,subset_class_def,GSYM RIGHT_EXISTS_AND_THM] >>
        rw[] >> qspecl_then [`n`,`m_s`,`m_o`,`m_a`,`m_r`] mp_tac sigma_algebra_traj_sig_alg_n >>
        simp[] >> strip_tac >> dxrule_then mp_tac SIGMA_ALGEBRA_SUBSET_CLASS >> simp[subset_class_def] >>
        strip_tac >> NTAC 4 $ irule_at Any SUBSET_CROSS >> simp[MEASURABLE_SETS_SUBSET_SPACE])
    >- simp[MEASURE_SPACE_SUBSET_CLASS,subset_class_step_rect_sets_n]
    >- (rename [`hs × ws × as × ss × rs`] >> simp[in_step_rect_sets_n] >>
        qexistsl_tac [`hs`,`ws`,`as`,`ss`,`rs`] >> simp[])
    >- (simp[GSYM RIGHT_EXISTS_AND_THM] >> gvs[in_step_rect_sets_n] >>
        qexistsl_tac [`hs`,`ws`,`as`,`ss`,`rs`] >> simp[] >> dxrule_then irule BIJ_PREIMAGE_IMAGE >>
        simp[m_space_prod_measure_space] >> NTAC 4 $ irule_at Any SUBSET_CROSS >>
        simp[MEASURABLE_SETS_SUBSET_SPACE] >>
        qspecl_then [`n`,`m_s`,`m_o`,`m_a`,`m_r`] mp_tac sigma_algebra_traj_sig_alg_n >>
        simp[] >> strip_tac >> dxrule_then mp_tac SIGMA_ALGEBRA_SUBSET_CLASS >> simp[subset_class_def])
QED

Theorem traj_measure_space_n_iso:
    (∀(m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space).
        measure_space m_s ∧ measure_space m_o ∧ measure_space m_a ∧ measure_space m_r ⇒
        isomorphic (traj_measure_space_n 0 m_s m_o m_a m_r) m_s) ∧
    (∀n (m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space).
        sigma_finite_measure_space m_s ∧ sigma_finite_measure_space m_o ∧
        sigma_finite_measure_space m_a ∧ sigma_finite_measure_space m_r ∧
        sigma_finite_measure_space (traj_measure_space_n n m_s m_o m_a m_r) ⇒
        isomorphic (traj_measure_space_n (SUC n) m_s m_o m_a m_r)
        (traj_measure_space_n n m_s m_o m_a m_r × m_o × m_a × m_s × m_r))
Proof
    CONJ_TAC >> rw[] >> irule isomorphic_sym_imp >> simp[isomorphic_def]
    >- (qexists_tac `init` >> simp[in_measure_preserving_init])
    >- (qexists_tac `λ(h,w,a,s,r). tcons h w a s r` >> simp[in_measure_preserving_tcons])
QED

Theorem sigma_finite_measure_space_traj_measure_space_n:
    ∀n (m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space).
        sigma_finite_measure_space m_s ∧ sigma_finite_measure_space m_o ∧
        sigma_finite_measure_space m_a ∧ sigma_finite_measure_space m_r ⇒
        sigma_finite_measure_space (traj_measure_space_n n m_s m_o m_a m_r)
Proof
    rw[] >> Induct_on `n`
    >- (irule $ INST_TYPE [``:α`` |-> ``:σ``] sigma_finite_measure_space_isomorphic >>
        qexists_tac `m_s` >> simp[] >> irule isomorphic_sym_imp >> simp[traj_measure_space_n_iso])
    >- (irule $ INST_TYPE [``:α`` |-> ``:(α,ρ,σ,ω) traj # ω # α # σ # ρ``] sigma_finite_measure_space_isomorphic >>
        qexists_tac `traj_measure_space_n n m_s m_o m_a m_r × m_o × m_a × m_s × m_r` >>
        irule_at Any isomorphic_sym_imp >> simp[traj_measure_space_n_iso] >>
        NTAC 4 (irule sigma_finite_measure_space_prod_measure >> simp[]))
QED

Theorem in_measure_preserving_tcons:
    ∀n (m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space).
        sigma_finite_measure_space m_s ∧ sigma_finite_measure_space m_o ∧
        sigma_finite_measure_space m_a ∧ sigma_finite_measure_space m_r ⇒
        (λ(h,w,a,s,r). tcons h w a s r) ∈ measure_preserving
        (traj_measure_space_n n m_s m_o m_a m_r × m_o × m_a × m_s × m_r)
        (traj_measure_space_n (SUC n) m_s m_o m_a m_r)
Proof
    rw[] >> irule in_measure_preserving_tcons >> simp[sigma_finite_measure_space_traj_measure_space_n]
QED

Theorem traj_measure_space_n_iso:
    (∀(m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space).
        measure_space m_s ∧ measure_space m_o ∧ measure_space m_a ∧ measure_space m_r ⇒
        isomorphic (traj_measure_space_n 0 m_s m_o m_a m_r) m_s) ∧
    (∀n (m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space).
        sigma_finite_measure_space m_s ∧ sigma_finite_measure_space m_o ∧
        sigma_finite_measure_space m_a ∧ sigma_finite_measure_space m_r ⇒
        isomorphic (traj_measure_space_n (SUC n) m_s m_o m_a m_r)
        (traj_measure_space_n n m_s m_o m_a m_r × m_o × m_a × m_s × m_r))
Proof
    CONJ_TAC >> rw[] >> irule isomorphic_sym_imp >> simp[isomorphic_def]
    >- (qexists_tac `init` >> simp[in_measure_preserving_init])
    >- (qexists_tac `λ(h,w,a,s,r). tcons h w a s r` >> simp[in_measure_preserving_tcons])
QED

Theorem measure_space_traj_measure_space_n:
    ∀n (m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space).
        sigma_finite_measure_space m_s ∧ sigma_finite_measure_space m_o ∧
        sigma_finite_measure_space m_a ∧ sigma_finite_measure_space m_r ⇒
        measure_space (traj_measure_space_n n m_s m_o m_a m_r)
Proof
    rw[] >> irule sigma_finite_measure_space_measure_space >>
    simp[sigma_finite_measure_space_traj_measure_space_n]
QED

Theorem measure_space_traj_measure_space_0:
    ∀(m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space).
        measure_space m_s ∧ measure_space m_o ∧ measure_space m_a ∧ measure_space m_r ⇒
        measure_space (traj_measure_space_n 0 m_s m_o m_a m_r)
Proof
    rw[] >>
    resolve_then Any (resolve_then Any (irule_at Any) (cj 1 traj_measure_space_n_iso))
        isomorphic_sym_imp measure_space_isomorphic >>
    simp[]
QED

Theorem traj_tonelli_0:
    ∀(m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space) f.
        measure_space m_s ∧ measure_space m_o ∧ measure_space m_a ∧ measure_space m_r ∧
        (∀h. h ∈ traj_m_space_n 0 m_s m_o m_a m_r ⇒ 0 ≤ f h) ∧
        f ∈ Borel_measurable (traj_sig_alg_n 0 m_s m_o m_a m_r) ⇒
        ∫⁺ (traj_measure_space_n 0 m_s m_o m_a m_r) f = ∫⁺ m_s (f ∘ init)
Proof
    rw[] >> irule iso_pos_fn_integral_comp >> simp[] >>
    irule_at Any $ INST_TYPE [``:α`` |-> ``:σ``,``:β`` |-> ``:(α,ρ,σ,ω) traj``] measure_space_isomorphic >>
    qexists_tac `m_s` >> simp[isomorphic_def] >> CONJ_ASM2_TAC
    >- (qexists_tac `init` >> simp[]) >>
    simp[in_measure_preserving_init]
QED

Theorem traj_tonelli_SUC:
    ∀n (m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space) f.
        sigma_finite_measure_space m_s ∧ sigma_finite_measure_space m_o ∧
        sigma_finite_measure_space m_a ∧ sigma_finite_measure_space m_r ∧
        (∀h. h ∈ traj_m_space_n (SUC n) m_s m_o m_a m_r ⇒ 0 ≤ f h) ∧
        f ∈ Borel_measurable (traj_sig_alg_n (SUC n) m_s m_o m_a m_r) ⇒
        ∫⁺ (traj_measure_space_n (SUC n) m_s m_o m_a m_r) f = ∫⁺ (traj_measure_space_n n m_s m_o m_a m_r) (λh.
        ∫⁺ m_o (λw. ∫⁺ m_a (λa. ∫⁺ m_s (λs. ∫⁺ m_r (λr. f (tcons h w a s r))))))
Proof
    rw[] >> irule EQ_TRANS >>
    qexists_tac `∫⁺ (traj_measure_space_n n m_s m_o m_a m_r × m_o × m_a × m_s × m_r)
        (f ∘ (λ(h,w,a,s,r). tcons h w a s r))` >>
    irule_at Any iso_pos_fn_integral_comp >> simp[in_measure_preserving_tcons] >>
    irule_at (Pos (el 1)) $ INST_TYPE [``:α`` |-> ``:(α,ρ,σ,ω) traj``,
        ``:β`` |-> ``:(α,ρ,σ,ω) traj # ω # α # σ # ρ``] measure_space_isomorphic >>
    qexists_tac `(traj_measure_space_n (SUC n) m_s m_o m_a m_r)` >>
    csimp[traj_measure_space_n_iso,measure_space_traj_measure_space_n] >>
    `∀h w a s r. h ∈ traj_m_space_n n m_s m_o m_a m_r ∧ w ∈ m_space m_o ∧
      a ∈ m_space m_a ∧ s ∈ m_space m_s ∧ r ∈ m_space m_r ⇒ 0 ≤ f (tcons h w a s r)` by (rw[] >>
        first_x_assum irule >> simp[in_traj_m_space_n]) >>
    qpat_x_assum `∀h. _ ⇒ 0 ≤ f h` kall_tac >>
    `sigma_finite_measure_space (m_s × m_r) ∧ sigma_finite_measure_space (m_a × m_s × m_r) ∧
      sigma_finite_measure_space (m_o × m_a × m_s × m_r)` by simp[sigma_finite_measure_space_prod_measure] >>
    `sigma_finite_measure_space (traj_measure_space_n n m_s m_o m_a m_r)`
        by simp[sigma_finite_measure_space_traj_measure_space_n] >>
    `(λ(h,w,a,s,r). tcons h w a s r) ∈ measurable
      (sig_alg ((traj_measure_space_n n m_s m_o m_a m_r × m_o × m_a × m_s × m_r)))
      (traj_sig_alg_n (SUC n) m_s m_o m_a m_r)` by (irule measurability_preserving_measurable >>
        qspecl_then [`n`,`m_s`,`m_o`,`m_a`,`m_r`] mp_tac in_measure_preserving_tcons >>
        simp[in_measure_preserving]) >>
    dxrule_all_then assume_tac MEASURABLE_COMP >>
    `(f ∘ (λ(h,w,a,s,r). tcons h w a s r)) = (λ(h,w,a,s,r). f (tcons h w a s r))` by simp[FUN_EQ_THM,UNCURRY] >>
    pop_assum SUBST_ALL_TAC >> fs[Once sig_alg_prod_measure_space,Excl "sig_alg_traj_measure_space"] >>
    dxrule_at_then (Pos (el 3)) (fn th => assume_tac (cj 2 th) >> assume_tac (cj 6 th)) TONELLI_ALT >>
    rfs[FORALL_PROD,in_mspace_prod_measure_space] >> pop_assum kall_tac >>
    NTAC 3 (irule_at Any pos_fn_integral_cong >> csimp[GSYM FORALL_IMP_CONJ_THM] >> gen_tac >> DISCH_TAC >>
        first_x_assum $ drule_then assume_tac >> fs[Once sig_alg_prod_measure_space] >>
        dxrule_at_then (Pos (el 3)) (fn th => assume_tac (cj 2 th) >> assume_tac (cj 6 th)) TONELLI_ALT >>
        rfs[FORALL_PROD,in_mspace_prod_measure_space] >> pop_assum kall_tac >> irule_at Any pos_fn_integral_pos) >>
    rw[] >> irule_at Any pos_fn_integral_pos >> simp[]
QED

Theorem traj_tonelli_SUC_step:
    ∀n (m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space) f.
        sigma_finite_measure_space m_s ∧ sigma_finite_measure_space m_o ∧
        sigma_finite_measure_space m_a ∧ sigma_finite_measure_space m_r ∧
        (∀h. h ∈ traj_m_space_n (SUC n) m_s m_o m_a m_r ⇒ 0 ≤ f h) ∧
        f ∈ Borel_measurable (traj_sig_alg_n (SUC n) m_s m_o m_a m_r) ⇒
        ∫⁺ (traj_measure_space_n (SUC n) m_s m_o m_a m_r) f = ∫⁺ (traj_measure_space_n n m_s m_o m_a m_r) (λh.
        ∫⁺ (m_o × m_a × m_s × m_r) (λ(w,a,s,r). f (tcons h w a s r)))
Proof
    rw[] >> irule EQ_TRANS >>
    qexists_tac `∫⁺ (traj_measure_space_n n m_s m_o m_a m_r × m_o × m_a × m_s × m_r)
        (f ∘ (λ(h,w,a,s,r). tcons h w a s r))` >>
    irule_at Any iso_pos_fn_integral_comp >> simp[in_measure_preserving_tcons] >>
    irule_at (Pos (el 1)) $ INST_TYPE [``:α`` |-> ``:(α,ρ,σ,ω) traj``,
        ``:β`` |-> ``:(α,ρ,σ,ω) traj # ω # α # σ # ρ``] measure_space_isomorphic >>
    qexists_tac `(traj_measure_space_n (SUC n) m_s m_o m_a m_r)` >>
    csimp[traj_measure_space_n_iso,measure_space_traj_measure_space_n] >>
    `(f ∘ (λ(h,w,a,s,r). tcons h w a s r)) = (λ(h,w,a,s,r). f (tcons h w a s r))` by simp[FUN_EQ_THM,UNCURRY] >>
    pop_assum SUBST_ALL_TAC >>
    qspecl_then [`traj_measure_space_n n m_s m_o m_a m_r`,`m_o × m_a × m_s × m_r`,
        `(λ(h,w,a,s,r). f (tcons h w a s r))`] (assume_tac) $ cj 6 TONELLI_ALT >>
    `∀x. (λy. (λ(h,w,a,s,r). f (tcons h w a s r)) (x,y)) = (λ(w,a,s,r). f (tcons x w a s r))`
        by simp[FUN_EQ_THM,UNCURRY] >>
    fs[] >> pop_assum kall_tac >> pop_assum irule >>
    simp[sigma_finite_measure_space_traj_measure_space_n,sigma_finite_measure_space_prod_measure] >>
    first_assum $ C (resolve_then (Pos $ el 3) (irule_at Any)) IN_MEASURABLE_BOREL_COMP >>
    qexists_tac `(λ(h,w,a,s,r). tcons h w a s r)` >>
    simp[sig_alg_prod_measure_space,SPACE_PROD_SIGMA,FORALL_PROD,m_space_prod_measure_space] >>
    rpt (irule_at Any SIGMA_ALGEBRA_PROD_SIGMA_WEAK) >> simp[sigma_algebra_traj_sig_alg_n] >>
    resolve_then Any (irule_at Any o SIMP_RULE (srw_ss ()) [sig_alg_prod_measure_space])
        in_measure_preserving_tcons measure_preserving_measurable >>
    rw[] >> first_x_assum irule >> simp[in_traj_m_space_n]
QED

Definition traj_state_def:
    t_st (init s) = s ∧
    t_st (tcons (h: (α,ρ,σ,ω) traj) w a s r) = s
End

Definition traj_obs_def:
    t_obs (tcons (h: (α,ρ,σ,ω) traj) w a s r) = w
End

Definition traj_action_def:
    t_act (tcons (h: (α,ρ,σ,ω) traj) w a s r) = a
End

Definition traj_reward_def:
    t_rew (tcons (h: (α,ρ,σ,ω) traj) w a s r) = r
End

Definition traj_traj_def:
    t_traj (tcons (h: (α,ρ,σ,ω) traj) w a s r) = h
End

Theorem traj_state_in_m_space:
    ∀m_s m_o m_a m_r (h: (α,ρ,σ,ω) traj).
        h ∈ traj_m_space m_s m_o m_a m_r ⇒ t_st h ∈ m_space m_s
Proof
    rpt gen_tac >> Cases_on `h` >> simp[in_traj_m_space,traj_state_def]
QED

Theorem traj_state_n_in_m_space:
    ∀n m_s m_o m_a m_r (h: (α,ρ,σ,ω) traj).
        h ∈ traj_m_space_n n m_s m_o m_a m_r ⇒ t_st h ∈ m_space m_s
Proof
    rpt gen_tac >> Cases_on `h` >> Cases_on `n` >> simp[in_traj_m_space_n,traj_state_def]
QED

Theorem traj_m_space_n_num_steps:
    ∀n m_s m_o m_a m_r (h: (α,ρ,σ,ω) traj). h ∈ traj_m_space_n n m_s m_o m_a m_r ⇒ num_steps h = n
Proof
    Induct_on `n` >> rw[] >> Cases_on `h` >> fs[in_traj_m_space_n,num_steps_def,SF SFY_ss]
QED

Theorem num_steps_measurable:
    ∀m n (m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space).
        measure_space m_s ∧ measure_space m_o ∧ measure_space m_a ∧ measure_space m_r ⇒
        {h | num_steps h = m} ∩ traj_m_space_n n m_s m_o m_a m_r ∈ traj_measurable_sets_n n m_s m_o m_a m_r
Proof
    rw[] >> qspecl_then [`n`,`m_s`,`m_o`,`m_a`,`m_r`] assume_tac sigma_algebra_traj_sig_alg_n >>
    rfs[] >> Cases_on `m = n` >> rw[]
    >- (`{h | num_steps h = m} ∩ traj_m_space_n m m_s m_o m_a m_r =
          traj_m_space_n m m_s m_o m_a m_r` suffices_by (DISCH_THEN SUBST1_TAC >>
            dxrule_then mp_tac SIGMA_ALGEBRA_SPACE >> simp[]) >>
        irule SUBSET_INTER2 >> simp[SUBSET_DEF,traj_m_space_n_num_steps,SF SFY_ss])
    >- (`{h | num_steps h = m} ∩ traj_m_space_n n m_s m_o m_a m_r = ∅` suffices_by (
            DISCH_THEN SUBST1_TAC >> dxrule_then mp_tac SIGMA_ALGEBRA_EMPTY >> simp[]) >>
        simp[GSYM DISJOINT_DEF,Once DISJOINT_SYM,DISJOINT_ALT] >>
        rw[] >> dxrule_then SUBST1_TAC traj_m_space_n_num_steps >> simp[])
QED

Theorem traj_state_measurable:
    ∀n (m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space).
        measure_space m_s ∧ measure_space m_o ∧ measure_space m_a ∧ measure_space m_r ⇒
        t_st ∈ measurable (traj_sig_alg_n n m_s m_o m_a m_r) (sig_alg m_s)
Proof
    rw[] >> simp[measurable_def,sigma_algebra_traj_sig_alg_n] >> CONJ_TAC
    >- (simp[FUNSET] >> qx_gen_tac `h` >> Cases_on `h` >> Cases_on `n` >>
        simp[in_traj_m_space_n,traj_state_def]) >>
    qx_gen_tac `ss` >> strip_tac >> Cases_on `n`
    >| [qabbrev_tac `(hr: (α -> bool, ρ -> bool, σ -> bool, ω -> bool) traj) = init ss`,
        rename [`SUC n`] >>
        qabbrev_tac `hr = tcons (traj_n_gen n (m_space m_s) (m_space m_o) (m_space m_a) (m_space m_r))
            (m_space m_o) (m_space m_a) ss (m_space m_r)`] >>
    qmatch_abbrev_tac `hs ∈ _` >>
    `hs = traj_cross hr` by (UNABBREV_ALL_TAC >> simp[EXTENSION] >> qx_gen_tac `h` >> Cases_on `h` >>
        simp[in_traj_m_space_n,traj_state_def,in_traj_cross,GSYM traj_m_space_n_def] >>
        `∀s. s ∈ ss ⇒ s ∈ m_space m_s` suffices_by (rw[] >> eq_tac >> rw[]) >>
        simp[GSYM SUBSET_DEF,MEASURABLE_SETS_SUBSET_SPACE]) >>
    pop_assum SUBST1_TAC >> qunabbrev_tac `hs` >>
    irule $ SIMP_RULE (srw_ss ()) [SUBSET_DEF] traj_rect_set_n_measurable >>
    simp[traj_rect_sets_n_def,traj_n_gen_def] >> qexists_tac `hr` >>
    simp[Abbr `hr`,in_traj_cross,MEASURE_SPACE_SPACE,GSYM traj_m_space_n_def] >>
    Induct_on `n` >> simp[traj_n_gen_def,in_traj_cross,MEASURE_SPACE_SPACE]
QED

Theorem traj_obs_measurable:
    ∀n (m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space).
        measure_space m_s ∧ measure_space m_o ∧ measure_space m_a ∧ measure_space m_r ⇒
        t_obs ∈ measurable (traj_sig_alg_n (SUC n) m_s m_o m_a m_r) (sig_alg m_o)
Proof
    rw[] >> simp[measurable_def,sigma_algebra_traj_sig_alg_n] >> CONJ_TAC
    >- (simp[FUNSET] >> qx_gen_tac `h` >> Cases_on `h` >> simp[in_traj_m_space_n,traj_obs_def]) >>
    qx_gen_tac `ws` >> strip_tac >> qmatch_abbrev_tac `hs ∈ _` >>
    qabbrev_tac `hr = tcons (traj_n_gen n (m_space m_s) (m_space m_o) (m_space m_a) (m_space m_r))
        ws (m_space m_a) (m_space m_s) (m_space m_r)` >>
    `hs = traj_cross hr` by (UNABBREV_ALL_TAC >> simp[EXTENSION] >> qx_gen_tac `h` >> Cases_on `h` >>
        simp[in_traj_m_space_n,traj_obs_def,in_traj_cross,GSYM traj_m_space_n_def] >>
        `∀w. w ∈ ws ⇒ w ∈ m_space m_o` suffices_by (rw[] >> eq_tac >> rw[]) >>
        simp[GSYM SUBSET_DEF,MEASURABLE_SETS_SUBSET_SPACE]) >>
    pop_assum SUBST1_TAC >> qunabbrev_tac `hs` >>
    irule $ SIMP_RULE (srw_ss ()) [SUBSET_DEF] traj_rect_set_n_measurable >>
    simp[traj_rect_sets_n_def,traj_n_gen_def] >> qexists_tac `hr` >>
    simp[Abbr `hr`,in_traj_cross,MEASURE_SPACE_SPACE,GSYM traj_m_space_n_def] >>
    Induct_on `n` >> simp[traj_n_gen_def,in_traj_cross,MEASURE_SPACE_SPACE]
QED

Theorem traj_action_measurable:
    ∀n (m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space).
        measure_space m_s ∧ measure_space m_o ∧ measure_space m_a ∧ measure_space m_r ⇒
        t_act ∈ measurable (traj_sig_alg_n (SUC n) m_s m_o m_a m_r) (sig_alg m_a)
Proof
    rw[] >> simp[measurable_def,sigma_algebra_traj_sig_alg_n] >> CONJ_TAC
    >- (simp[FUNSET] >> qx_gen_tac `h` >> Cases_on `h` >> simp[in_traj_m_space_n,traj_action_def]) >>
    qx_gen_tac `as` >> strip_tac >> qmatch_abbrev_tac `hs ∈ _` >>
    qabbrev_tac `hr = tcons (traj_n_gen n (m_space m_s) (m_space m_o) (m_space m_a) (m_space m_r))
        (m_space m_o) as (m_space m_s) (m_space m_r)` >>
    `hs = traj_cross hr` by (UNABBREV_ALL_TAC >> simp[EXTENSION] >> qx_gen_tac `h` >> Cases_on `h` >>
        simp[in_traj_m_space_n,traj_action_def,in_traj_cross,GSYM traj_m_space_n_def] >>
        `∀a. a ∈ as ⇒ a ∈ m_space m_a` suffices_by (rw[] >> eq_tac >> rw[]) >>
        simp[GSYM SUBSET_DEF,MEASURABLE_SETS_SUBSET_SPACE]) >>
    pop_assum SUBST1_TAC >> qunabbrev_tac `hs` >>
    irule $ SIMP_RULE (srw_ss ()) [SUBSET_DEF] traj_rect_set_n_measurable >>
    simp[traj_rect_sets_n_def,traj_n_gen_def] >> qexists_tac `hr` >>
    simp[Abbr `hr`,in_traj_cross,MEASURE_SPACE_SPACE,GSYM traj_m_space_n_def] >>
    Induct_on `n` >> simp[traj_n_gen_def,in_traj_cross,MEASURE_SPACE_SPACE]
QED

Theorem traj_reward_measurable:
    ∀n (m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space).
        measure_space m_s ∧ measure_space m_o ∧ measure_space m_a ∧ measure_space m_r ⇒
        t_rew ∈ measurable (traj_sig_alg_n (SUC n) m_s m_o m_a m_r) (sig_alg m_r)
Proof
    rw[] >> simp[measurable_def,sigma_algebra_traj_sig_alg_n] >> CONJ_TAC
    >- (simp[FUNSET] >> qx_gen_tac `h` >> Cases_on `h` >> simp[in_traj_m_space_n,traj_reward_def]) >>
    qx_gen_tac `rs` >> strip_tac >> qmatch_abbrev_tac `hs ∈ _` >>
    qabbrev_tac `hr = tcons (traj_n_gen n (m_space m_s) (m_space m_o) (m_space m_a) (m_space m_r))
        (m_space m_o) (m_space m_a) (m_space m_s) rs` >>
    `hs = traj_cross hr` by (UNABBREV_ALL_TAC >> simp[EXTENSION] >> qx_gen_tac `h` >> Cases_on `h` >>
        simp[in_traj_m_space_n,traj_reward_def,in_traj_cross,GSYM traj_m_space_n_def] >>
        `∀r. r ∈ rs ⇒ r ∈ m_space m_r` suffices_by (rw[] >> eq_tac >> rw[]) >>
        simp[GSYM SUBSET_DEF,MEASURABLE_SETS_SUBSET_SPACE]) >>
    pop_assum SUBST1_TAC >> qunabbrev_tac `hs` >>
    irule $ SIMP_RULE (srw_ss ()) [SUBSET_DEF] traj_rect_set_n_measurable >>
    simp[traj_rect_sets_n_def,traj_n_gen_def] >> qexists_tac `hr` >>
    simp[Abbr `hr`,in_traj_cross,MEASURE_SPACE_SPACE,GSYM traj_m_space_n_def] >>
    Induct_on `n` >> simp[traj_n_gen_def,in_traj_cross,MEASURE_SPACE_SPACE]
QED

Theorem traj_traj_measurable:
    ∀n (m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space).
        measure_space m_s ∧ measure_space m_o ∧ measure_space m_a ∧ measure_space m_r ⇒
        t_traj ∈ measurable (traj_sig_alg_n (SUC n) m_s m_o m_a m_r) (traj_sig_alg_n n m_s m_o m_a m_r)
Proof
    rw[] >> simp[measurable_def,sigma_algebra_traj_sig_alg_n] >> CONJ_TAC
    >- (simp[FUNSET] >> qx_gen_tac `h` >> Cases_on `h` >> simp[in_traj_m_space_n,traj_traj_def]) >>
    qx_gen_tac `hs` >> strip_tac >> qmatch_abbrev_tac `hsp ∈ _` >>
    qabbrev_tac `hr = step_cross hs (m_space m_o) (m_space m_a) (m_space m_s) (m_space m_r)` >>
    `hsp = hr` by (UNABBREV_ALL_TAC >> simp[EXTENSION] >> qx_gen_tac `h` >> Cases_on `h` >>
        simp[in_traj_m_space_n,traj_traj_def,in_step_cross,GSYM traj_m_space_n_def] >>
        `∀h. h ∈ hs ⇒ h ∈ traj_m_space_n n m_s m_o m_a m_r` suffices_by (rw[] >> eq_tac >> rw[]) >>
        `sigma_algebra (traj_sig_alg_n n m_s m_o m_a m_r)` by simp[sigma_algebra_traj_sig_alg_n] >>
        dxrule_then mp_tac SIGMA_ALGEBRA_SUBSET_SPACE >> simp[GSYM SUBSET_DEF]) >>
    pop_assum SUBST1_TAC >> qunabbrev_tac `hsp` >>
    irule $ SIMP_RULE (srw_ss ()) [SUBSET_DEF] step_rect_set_n_measurable >>
    simp[step_rect_sets_n_def] >> qunabbrev_tac `hr` >>
    qexistsl_tac [`hs`,`m_space m_o`,`m_space m_a`,`m_space m_s`,`m_space m_r`] >>
    simp[MEASURE_SPACE_SPACE]
QED

Definition valid_dist_gen_funs_def:
    valid_dist_gen_funs (m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space) d0 P Z R bet ⇔
        (∀s. s ∈ m_space m_s ⇒ 0 ≤ d0 s ∧ d0 s ≠ +∞) ∧
        (∀s a t. s ∈ m_space m_s ∧ a ∈ m_space m_a ∧ t ∈ m_space m_s ⇒ 0 ≤ P s a t ∧ P s a t ≠ +∞) ∧
        (∀s w. s ∈ m_space m_s ∧ w ∈ m_space m_o ⇒ 0 ≤ Z s w ∧ Z s w ≠ +∞) ∧
        (∀s a t r. s ∈ m_space m_s ∧ a ∈ m_space m_a ∧ t ∈ m_space m_s ∧ r ∈ m_space m_r ⇒
             0 ≤ R s a t r ∧ R s a t r ≠ +∞) ∧
        (∀w a. w ∈ m_space m_o ∧ a ∈ m_space m_a ⇒ 0 ≤ bet w a ∧ bet w a ≠ +∞) ∧
        d0 ∈ Borel_measurable (sig_alg m_s) ∧
        (λ(s,a,t). P s a t) ∈ Borel_measurable (sig_alg (m_s × m_a × m_s)) ∧
        (λ(s,w). Z s w) ∈ Borel_measurable (sig_alg (m_s × m_o)) ∧
        (λ(s,a,t,r). R s a t r) ∈ Borel_measurable (sig_alg (m_s × m_a × m_s × m_r)) ∧
        (λ(w,a). bet w a) ∈ Borel_measurable (sig_alg (m_o × m_a)) ∧
        (prob_space (density m_s d0)) ∧
        (∀s a. s ∈ m_space m_s ∧ a ∈ m_space m_a ⇒ prob_space (density m_s (P s a))) ∧
        (∀s. s ∈ m_space m_s ⇒ prob_space (density m_o (Z s))) ∧
        (∀s a t. s ∈ m_space m_s ∧ a ∈ m_space m_a ∧ t ∈ m_space m_s ⇒ prob_space (density m_r (R s a t))) ∧
        (∀w. w ∈ m_space m_o ⇒ prob_space (density m_a (bet w)))
End

Theorem valid_dist_gen_funs_m_s_non_empty:
    ∀(m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space) d0 P Z R bet.
        valid_dist_gen_funs m_s m_o m_a m_r d0 P Z R bet ⇒ m_space m_s ≠ ∅
Proof
    rw[valid_dist_gen_funs_def] >> dxrule_then mp_tac prob_space_not_empty >> simp[p_space_def]
QED

Definition traj_pdf_def:
    traj_pdf d0 P Z R bet (init s) = d0 s:extreal ∧
    traj_pdf d0 P Z R bet (tcons (h: (α,ρ,σ,ω) traj) w a s r) =
        traj_pdf d0 P Z R bet h * Z (t_st h) w * bet w a * P (t_st h) a s * R (t_st h) a s r
End

Theorem traj_pdf_pos:
    ∀m_s m_o m_a m_r d0 P Z R bet (h: (α,ρ,σ,ω) traj). valid_dist_gen_funs m_s m_o m_a m_r d0 P Z R bet ∧
        h ∈ traj_m_space m_s m_o m_a m_r ⇒ 0 ≤ traj_pdf d0 P Z R bet h
Proof
    rpt gen_tac >> Induct_on `h` >> rw[in_traj_m_space] >> fs[valid_dist_gen_funs_def,traj_pdf_def] >>
    NTAC 4 $ irule_at Any le_mul >> simp[traj_state_in_m_space,SF SFY_ss]
QED

Theorem traj_pdf_n_pos:
    ∀n m_s m_o m_a m_r d0 P Z R bet (h: (α,ρ,σ,ω) traj). valid_dist_gen_funs m_s m_o m_a m_r d0 P Z R bet ∧
        h ∈ traj_m_space_n n m_s m_o m_a m_r ⇒ 0 ≤ traj_pdf d0 P Z R bet h
Proof
    rw[] >> irule traj_pdf_pos >> qexistsl_tac [`m_a`,`m_o`,`m_r`,`m_s`] >>
    simp[SIMP_RULE (srw_ss ()) [SUBSET_DEF] traj_m_space_n_subset_traj_m_space,SF SFY_ss]
QED

Theorem traj_pdf_not_infty:
    ∀m_s m_o m_a m_r d0 P Z R bet (h: (α,ρ,σ,ω) traj). valid_dist_gen_funs m_s m_o m_a m_r d0 P Z R bet ∧
        h ∈ traj_m_space m_s m_o m_a m_r ⇒ traj_pdf d0 P Z R bet h ≠ +∞
Proof
    rpt gen_tac >> Induct_on `h` >> rw[in_traj_m_space]
    >| [all_tac,drule_all_then assume_tac traj_pdf_pos] >> fs[valid_dist_gen_funs_def,traj_pdf_def] >>
    `∀x y. 0 ≤ x ∧ x ≠ +∞ ∧ 0 ≤ y ∧ y ≠ +∞ ⇒ x * y ≠ +∞` by (rpt $ pop_assum kall_tac >>
        rw[] >> irule $ cj 2 mul_not_infty2 >> simp[pos_not_neginf]) >>
    pop_assum (fn th => irule_at Any th >> NTAC 3 (irule_at Any le_mul >> irule_at Any th)) >>
    simp[traj_state_in_m_space,SF SFY_ss]
QED

Theorem traj_pdf_n_not_infty:
    ∀n m_s m_o m_a m_r d0 P Z R bet (h: (α,ρ,σ,ω) traj). valid_dist_gen_funs m_s m_o m_a m_r d0 P Z R bet ∧
        h ∈ traj_m_space_n n m_s m_o m_a m_r ⇒ traj_pdf d0 P Z R bet h ≠ +∞
Proof
    rw[] >> irule traj_pdf_not_infty >> qexistsl_tac [`m_a`,`m_o`,`m_r`,`m_s`] >>
    simp[SIMP_RULE (srw_ss ()) [SUBSET_DEF] traj_m_space_n_subset_traj_m_space,SF SFY_ss]
QED

Theorem traj_pdf_abs_cont:
    ∀m_s m_o m_a m_r d0 P Z R bet phi (h: (α,ρ,σ,ω) traj). h ∈ traj_m_space m_s m_o m_a m_r ∧
        (∀w a. w ∈ m_space m_o ∧ a ∈ m_space m_a ∧ bet w a = 0 ⇒ phi w a = 0) ∧
        traj_pdf d0 P Z R bet h = 0 ⇒ traj_pdf d0 P Z R phi h = 0
Proof
    Induct_on `h` >> rw[traj_pdf_def,in_traj_m_space] >> fs[] >>
    last_x_assum $ dxrule_then $ dxrule_then assume_tac >> rfs[]
QED

Theorem traj_pdf_n_abs_cont:
    ∀n m_s m_o m_a m_r d0 P Z R bet phi (h: (α,ρ,σ,ω) traj). h ∈ traj_m_space_n n m_s m_o m_a m_r ∧
        (∀w a. w ∈ m_space m_o ∧ a ∈ m_space m_a ∧ bet w a = 0 ⇒ phi w a = 0) ∧
        traj_pdf d0 P Z R bet h = 0 ⇒ traj_pdf d0 P Z R phi h = 0
Proof
    rw[] >> irule traj_pdf_abs_cont >> qexistsl_tac [`bet`,`m_a`,`m_o`,`m_r`,`m_s`] >>
    simp[SIMP_RULE (srw_ss ()) [SUBSET_DEF] traj_m_space_n_subset_traj_m_space,SF SFY_ss]
QED

Theorem in_measurable_borel_tsan_traj_pdf:
    ∀n (m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space) d0 P Z R bet.
        measure_space m_s ∧ measure_space m_o ∧ measure_space m_a ∧ measure_space m_r ∧
        valid_dist_gen_funs m_s m_o m_a m_r d0 P Z R bet ⇒
        traj_pdf d0 P Z R bet ∈ Borel_measurable (traj_sig_alg_n n m_s m_o m_a m_r)
Proof
    rpt gen_tac >> DISCH_TAC >> fs[valid_dist_gen_funs_def] >>
    `∀n. sigma_algebra (traj_sig_alg_n n m_s m_o m_a m_r)` by simp[sigma_algebra_traj_sig_alg_n] >>
    Induct_on `n` >> rw[]
    >- (map_every (fn (pos,tm,qex,ths) => irule_at pos tm >> qexistsl_tac qex >> simp ths) [
            (Any,IN_MEASURABLE_BOREL_CONG,[`d0 ∘ t_st`],[]),
            (Any,INST_TYPE [``:α`` |-> ``:(α,ρ,σ,ω) traj``,``:β`` |-> ``:σ``] IN_MEASURABLE_BOREL_COMP,
                [`t_st`,`d0`,`sig_alg m_s`],[])] >>
        simp[traj_state_measurable] >> qx_gen_tac `h` >> Cases_on `h` >>
        simp[in_traj_m_space_n,traj_pdf_def,traj_state_def]) >>
    map_every qabbrev_tac [`pdf_rec = traj_pdf d0 P Z R bet ∘ t_traj`,
        `Z_rec = (λ(h: (α,ρ,σ,ω) traj). Z (t_st (t_traj h)) (t_obs h))`,
        `bet_rec = (λ(h: (α,ρ,σ,ω) traj). bet (t_obs h) (t_act h))`,
        `P_rec = (λ(h: (α,ρ,σ,ω) traj). P (t_st (t_traj h)) (t_act h) (t_st h))`,
        `R_rec = (λ(h: (α,ρ,σ,ω) traj). R (t_st (t_traj h)) (t_act h) (t_st h) (t_rew h))`] >>
    map_every (fn (pos,tm,qex,ths) => irule_at pos tm >> qexistsl_tac qex >> simp ths) [
        (Any,IN_MEASURABLE_BOREL_CONG,[`λh. pdf_rec h * Z_rec h * bet_rec h * P_rec h * R_rec h`],[]),
        (Any,IN_MEASURABLE_BOREL_MUL',[`R_rec`,`λh. pdf_rec h * Z_rec h * bet_rec h * P_rec h`],[]),
        (Pos hd,IN_MEASURABLE_BOREL_MUL',[`P_rec`,`λh. pdf_rec h * Z_rec h * bet_rec h`],[]),
        (Pos hd,IN_MEASURABLE_BOREL_MUL',[`bet_rec`,`λh. pdf_rec h * Z_rec h`],[]),
        (Pos hd,IN_MEASURABLE_BOREL_MUL',[`Z_rec`,`pdf_rec`],[]),
        (Pos hd,INST_TYPE [``:β`` |-> ``:α``] IN_MEASURABLE_BOREL_COMP,
            [`t_traj`,`traj_pdf d0 P Z R bet`,`traj_sig_alg_n n m_s m_o m_a m_r`],[Abbr `pdf_rec`]),
        (Pos (el 2),INST_TYPE [``:α`` |-> ``:(α,ρ,σ,ω) traj``,``:β`` |-> ``:σ # ω``] IN_MEASURABLE_BOREL_COMP,
            [`λh. (t_st (t_traj h),t_obs h)`,`λ(s,w). Z s w`,`sig_alg (m_s × m_o)`],
            [Abbr `Z_rec`,sig_alg_prod_measure_space]),
        (Pos hd,SIGMA_ALGEBRA_PROD_SIGMA_WEAK,[],[]),
        (Pos hd,IN_MEASURABLE_PROD_SIGMA,[`t_obs`,`t_st ∘ t_traj`],[]),
        (Pos (el 4),INST_TYPE [``:α`` |-> ``:(α,ρ,σ,ω) traj``,``:β`` |-> ``:ω # α``] IN_MEASURABLE_BOREL_COMP,
            [`λh. (t_obs h,t_act h)`,`λ(w,a). bet w a`,`sig_alg (m_o × m_a)`],
            [Abbr `bet_rec`,sig_alg_prod_measure_space]),
        (Pos hd,SIGMA_ALGEBRA_PROD_SIGMA_WEAK,[],[]),
        (Pos hd,IN_MEASURABLE_PROD_SIGMA,[`t_act`,`t_obs`],[SF CONJ_ss]),
        (Pos (el 5),INST_TYPE [``:α`` |-> ``:(α,ρ,σ,ω) traj``,``:β`` |-> ``:σ # α # σ``] IN_MEASURABLE_BOREL_COMP,
            [`λh. (t_st (t_traj h),t_act h,t_st h)`,`λ(s,a,t). P s a t`,`sig_alg (m_s × m_a × m_s)`],
            [Abbr `P_rec`,sig_alg_prod_measure_space]),
        (Pos hd,SIGMA_ALGEBRA_PROD_SIGMA_WEAK,[],[]),
        (Pos hd,SIGMA_ALGEBRA_PROD_SIGMA_WEAK,[],[]),
        (Pos hd,IN_MEASURABLE_PROD_SIGMA,[`λh. (t_act h,t_st h)`,`t_st ∘ t_traj`],[SF CONJ_ss]),
        (Pos hd,IN_MEASURABLE_PROD_SIGMA,[`t_st`,`t_act`],[SF CONJ_ss]),
        (Pos (el 6),
            INST_TYPE [``:α`` |-> ``:(α,ρ,σ,ω) traj``,``:β`` |-> ``:σ # α # σ # ρ``] IN_MEASURABLE_BOREL_COMP,
            [`λh. (t_st (t_traj h),t_act h,t_st h,t_rew h)`,`λ(s,a,t,r). R s a t r`,
              `sig_alg (m_s × m_a × m_s × m_r)`],
            [Abbr `R_rec`,sig_alg_prod_measure_space]),
        (Pos hd,SIGMA_ALGEBRA_PROD_SIGMA_WEAK,[],[]),
        (Pos hd,SIGMA_ALGEBRA_PROD_SIGMA_WEAK,[],[]),
        (Pos hd,SIGMA_ALGEBRA_PROD_SIGMA_WEAK,[],[]),
        (Pos hd,IN_MEASURABLE_PROD_SIGMA,[`λh. (t_act h,t_st h,t_rew h)`,`t_st ∘ t_traj`],[SF CONJ_ss]),
        (Pos hd,IN_MEASURABLE_PROD_SIGMA,[`λh. (t_st h,t_rew h)`,`t_act`],[SF CONJ_ss]),
        (Pos hd,IN_MEASURABLE_PROD_SIGMA,[`t_rew`,`t_st`],[SF CONJ_ss]),
        (Any,MEASURABLE_COMP,[`traj_sig_alg_n n m_s m_o m_a m_r`],[SF CONJ_ss])] >>
    simp[traj_state_measurable,traj_obs_measurable,traj_action_measurable,
        traj_reward_measurable,traj_traj_measurable] >>
    qx_gen_tac `h` >> Cases_on `h` >>
    simp[in_traj_m_space_n,traj_pdf_def,traj_state_def,traj_obs_def,traj_action_def,traj_reward_def,traj_traj_def]
QED

Theorem prob_space_traj_measure_space_n_pdf:
    ∀n (m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space) d0 P Z R bet.
        sigma_finite_measure_space m_s ∧ sigma_finite_measure_space m_o ∧
        sigma_finite_measure_space m_a ∧ sigma_finite_measure_space m_r ∧
        valid_dist_gen_funs m_s m_o m_a m_r d0 P Z R bet ⇒
        prob_space (density (traj_measure_space_n n m_s m_o m_a m_r) (traj_pdf d0 P Z R bet))
Proof
    rw[] >> irule_at Any prob_space_density >>
    simp[traj_pdf_n_pos,measure_space_traj_measure_space_n,SF SFY_ss] >>
    irule_at Any in_measurable_borel_tsan_traj_pdf >>
    simp[iffLR sigma_finite_measure_space_def] >> Induct_on `n` >> irule EQ_TRANS
    >- (qexists_tac `∫⁺ m_s (λs. traj_pdf d0 P Z R bet (init s))` >>
        simp[traj_pdf_def,ETA_AX] >> CONJ_TAC
        >- (irule EQ_TRANS >> qexists_tac `∫⁺ m_s (traj_pdf d0 P Z R bet ∘ init)` >>
            irule_at Any traj_tonelli_0 >>
            simp[in_measurable_borel_tsan_traj_pdf,traj_pdf_n_pos,o_DEF,traj_pdf_def,ETA_AX,SF SFY_ss]) >>
        fs[valid_dist_gen_funs_def] >> irule prob_space_density_pos_fn_integral_pdf >> simp[]) >>
    qexists_tac `∫⁺ (traj_measure_space_n n m_s m_o m_a m_r) (λh.
        ∫⁺ m_o (λw. ∫⁺ m_a (λa. ∫⁺ m_s (λs. ∫⁺ m_r (λr. traj_pdf d0 P Z R bet (tcons h w a s r))))))` >>
    CONJ_TAC >- (irule traj_tonelli_SUC >> simp[in_measurable_borel_tsan_traj_pdf,traj_pdf_n_pos,SF SFY_ss]) >>
    simp[traj_pdf_def] >> irule EQ_TRANS >>
    qexists_tac `∫⁺ (traj_measure_space_n n m_s m_o m_a m_r) (traj_pdf d0 P Z R bet)` >>
    irule_at Any pos_fn_integral_cong >> csimp[measure_space_traj_measure_space_n,GSYM FORALL_IMP_CONJ_THM] >>
    pop_assum kall_tac >> qx_gen_tac `h` >> DISCH_TAC >> CONJ_ASM1_TAC >- simp[traj_pdf_n_pos,SF SFY_ss] >>
    `t_st h ∈ m_space m_s` by simp[traj_state_n_in_m_space,SF SFY_ss] >>
    fs[sigma_finite_measure_space_def,valid_dist_gen_funs_def,sig_alg_prod_measure_space] >>
    NTAC 4 $ qpat_x_assum `sigma_finite _` kall_tac >>
    `(∀s a. s ∈ m_space m_s ∧ a ∈ m_space m_a ⇒ P s a ∈ Borel_measurable (sig_alg m_s)) ∧
      (∀s. s ∈ m_space m_s ⇒ Z s ∈ Borel_measurable (sig_alg m_o)) ∧
      (∀s a t. s ∈ m_space m_s ∧ a ∈ m_space m_a ∧ t ∈ m_space m_s ⇒ R s a t ∈ Borel_measurable (sig_alg m_r)) ∧
      (∀w. w ∈ m_space m_o ⇒ bet w ∈ Borel_measurable (sig_alg m_a))` by (
        rpt (first_x_assum $ C (resolve_then Any assume_tac) (cj 2 IN_MEASURABLE_BOREL_FROM_PROD_SIGMA_ALT) >>
            rfs[SIGMA_ALGEBRA_PROD_SIGMA_WEAK]) >>
        fs[SF ETA_ss]) >>
    NTAC 4 $ qpat_x_assum `_ ∈ Borel_measurable (a × b)` kall_tac >>
    map_every (fn (qex,tml,tm) => irule_at Any EQ_TRANS >> qexists_tac qex >>
        irule_at Any pos_fn_integral_cong >> csimp[] >>
        qspecl_then tml mp_tac pos_fn_integral_cmult_clean >>
        simp[prob_space_density_pos_fn_integral_pdf,SF SFY_ss] >> DISCH_THEN kall_tac >>
        simp[GSYM FORALL_IMP_CONJ_THM] >> qx_gen_tac tm >> DISCH_TAC >> CONJ_ASM1_TAC >- simp[le_mul])
        [(`∫⁺ m_o (λw. traj_pdf d0 P Z R bet h * Z (t_st h) w)`,
            [`m_o`,`Z (t_st h)`,`traj_pdf d0 P Z R bet h`],`w`),
        (`∫⁺ m_a (λa. traj_pdf d0 P Z R bet h * Z (t_st h) w * bet w a)`,
            [`m_a`,`bet w`,`traj_pdf d0 P Z R bet h * Z (t_st h) w`],`a`),
        (`∫⁺ m_s (λs. traj_pdf d0 P Z R bet h * Z (t_st h) w * bet w a * P (t_st h) a s)`,
            [`m_s`,`P (t_st h) a`,`traj_pdf d0 P Z R bet h * Z (t_st h) w * bet w a`],`s`)] >>
    qspecl_then [`m_r`,`R (t_st h) a s`,`traj_pdf d0 P Z R bet h * Z (t_st h) w * bet w a * P (t_st h) a s`]
        mp_tac pos_fn_integral_cmult_clean >>
    simp[prob_space_density_pos_fn_integral_pdf,SF SFY_ss]
QED

Theorem traj_pdf_tonelli_0:
    ∀(m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space) d0 P Z R bet f.
        measure_space m_s ∧ measure_space m_o ∧ measure_space m_a ∧ measure_space m_r ∧
        valid_dist_gen_funs m_s m_o m_a m_r d0 P Z R bet ∧
        (∀h. h ∈ traj_m_space_n 0 m_s m_o m_a m_r ⇒ 0 ≤ f h) ∧
        f ∈ Borel_measurable (traj_sig_alg_n 0 m_s m_o m_a m_r) ⇒
        ∫⁺ (density (traj_measure_space_n 0 m_s m_o m_a m_r) (traj_pdf d0 P Z R bet)) f =
        ∫⁺ (density m_s d0) (f ∘ init)
Proof
    rw[] >> qmatch_abbrev_tac `_ (_ m_t tpdf) _ = _ _ g` >>
    `∫⁺ (density m_t tpdf) f = ∫⁺ m_t (λh. tpdf h * f h) ∧ ∫⁺ (density m_s d0) g = ∫⁺ m_s (λs. d0 s * g s) ∧
        ∫⁺ m_t (λh. tpdf h * f h) = ∫⁺ m_s (λs. d0 s * g s)` suffices_by simp[] >>
    NTAC 2 $ irule_at Any pos_fn_integral_density_clean >> UNABBREV_ALL_TAC >> simp[] >>
    qspecl_then [`m_s`,`m_o`,`m_a`,`m_r`,`λh. traj_pdf d0 P Z R bet h * f h`]
        (irule_at Any o SIMP_RULE (srw_ss ()) [o_DEF,Abbr `tpdf`,traj_pdf_def]) traj_tonelli_0 >>
    resolve_then Any (resolve_then Any (irule_at Any) (cj 1 traj_measure_space_n_iso))
        isomorphic_sym_imp measure_space_isomorphic >>
    simp[traj_pdf_n_pos,le_mul,SF SFY_ss] >> irule_at Any MEASURABLE_COMP >>
    qexists_tac `traj_sig_alg_n 0 m_s m_o m_a m_r` >>
    qspecl_then [`m_s`,`m_o`,`m_a`,`m_r`] assume_tac in_measure_preserving_init >>
    rfs[in_measure_preserving] >> simp[measurability_preserving_measurable] >>
    irule_at (Pos $ el 1) IN_MEASURABLE_BOREL_MUL' >> qexistsl_tac [`f`,`traj_pdf d0 P Z R bet`] >>
    csimp[in_measurable_borel_tsan_traj_pdf] >> fs[in_measurability_preserving,BIJ_ALT,FUNSET,valid_dist_gen_funs_def]
QED

Definition importance_ratio_def:
    importance_ratio phi bet (init s) = 1:extreal ∧
    importance_ratio phi bet (tcons (h: (α,ρ,σ,ω) traj) w a s r) =
        importance_ratio phi bet h * phi w a * (bet w a)⁻¹
End

Theorem traj_ir_pos:
    ∀m_s m_o m_a m_r d0 P Z R bet phi (h: (α,ρ,σ,ω) traj). valid_dist_gen_funs m_s m_o m_a m_r d0 P Z R bet ∧
        valid_dist_gen_funs m_s m_o m_a m_r d0 P Z R phi ∧
        (∀w a. w ∈ m_space m_o ∧ a ∈ m_space m_a ∧ bet w a = 0 ⇒ phi w a = 0) ∧
        h ∈ traj_m_space m_s m_o m_a m_r ⇒ 0 ≤ importance_ratio phi bet h
Proof
    Induct_on `h` >> rw[importance_ratio_def,in_traj_m_space] >>
    last_x_assum $ drule_all_then assume_tac >> simp[Once $ GSYM mul_assoc] >> irule le_mul >>
    simp[] >> rename [`0 ≤ phi w a * _`] >> Cases_on `bet w a = 0` >> simp[] >> irule le_mul >>
    fs[valid_dist_gen_funs_def] >> irule le_inv >> simp[lt_le]
QED

Theorem traj_ir_n_pos:
    ∀n m_s m_o m_a m_r d0 P Z R bet phi (h: (α,ρ,σ,ω) traj). valid_dist_gen_funs m_s m_o m_a m_r d0 P Z R bet ∧
        valid_dist_gen_funs m_s m_o m_a m_r d0 P Z R phi ∧
        (∀w a. w ∈ m_space m_o ∧ a ∈ m_space m_a ∧ bet w a = 0 ⇒ phi w a = 0) ∧
        h ∈ traj_m_space_n n m_s m_o m_a m_r ⇒ 0 ≤ importance_ratio phi bet h
Proof
    rw[] >> dxrule_all_then assume_tac $ SIMP_RULE (srw_ss ()) [SUBSET_DEF] traj_m_space_n_subset_traj_m_space >>
    dxrule_all_then assume_tac traj_ir_pos >> simp[]
QED

(* done this way because of d0 s possibly being 0 in len 0 case *)
(* opeir proof pulls density function inside *)
Theorem importance_ratio_valid:
    ∀m_s m_o m_a m_r d0 P Z R bet phi (h: (α,ρ,σ,ω) traj).
        valid_dist_gen_funs m_s m_o m_a m_r d0 P Z R phi ∧
        h ∈ traj_m_space m_s m_o m_a m_r ∧ traj_pdf d0 P Z R bet h ≠ 0 ⇒
        traj_pdf d0 P Z R phi h * (traj_pdf d0 P Z R bet h)⁻¹ = importance_ratio phi bet h
Proof
    rw[traj_measure_space_def,valid_dist_gen_funs_def] >> Induct_on `h` >>
    rw[traj_pdf_def,importance_ratio_def] >> fs[in_traj_m_space]
    >- (irule mul_rinv_pos >> simp[lt_le]) >> dxrule_then assume_tac traj_state_in_m_space >>
    qpat_x_assum `_ = _` $ SUBST1_TAC o SYM >> simp[inv_mul] >>
    qmatch_abbrev_tac `xtp * xZ * xp * xP * xR * _ = xtp * xtb * xp * xb:extreal` >>
    `xZ * xZ⁻¹ = 1 ∧ xP * xP⁻¹ = 1 ∧ xR * xR⁻¹ = 1` suffices_by (
        strip_tac >> irule EQ_TRANS >>
        qexists_tac `xtp * xtb * xp * xb * (xZ * xZ⁻¹) * (xP * xP⁻¹) * (xR * xR⁻¹)` >>
        REVERSE CONJ_TAC >- simp[] >> rpt $ pop_assum kall_tac >>
        metis_tac[mul_assoc,mul_comm]) >>
    rw[] >> irule mul_rinv_pos >> UNABBREV_ALL_TAC >> simp[lt_le]
QED

Theorem importance_ratio_n_valid:
    ∀n m_s m_o m_a m_r d0 P Z R bet phi (h: (α,ρ,σ,ω) traj).
        valid_dist_gen_funs m_s m_o m_a m_r d0 P Z R phi ∧
        h ∈ traj_m_space_n n m_s m_o m_a m_r ∧ traj_pdf d0 P Z R bet h ≠ 0 ⇒
        traj_pdf d0 P Z R phi h * (traj_pdf d0 P Z R bet h)⁻¹ = importance_ratio phi bet h
Proof
    Induct_on `n` >> rw[] >> Cases_on `h` >> fs[traj_pdf_def,importance_ratio_def,in_traj_m_space_n] >> rw[]
    >- (irule mul_rinv_pos >> fs[valid_dist_gen_funs_def] >> simp[lt_le]) >>
    drule_then assume_tac traj_state_n_in_m_space >> rename [`R (t_st h) a t r ≠ 0`,`bet w a ≠ 0`] >>
    last_x_assum $ drule_then $ qspecl_then [`bet`,`h`] assume_tac >> rfs[] >>
    qpat_x_assum `_ = _` $ SUBST1_TAC o SYM >> simp[inv_mul] >>
    qmatch_abbrev_tac `xtp * xZ * xp * xP * xR * _ = xtp * xtb * xp * xb:extreal` >>
    `xZ * xZ⁻¹ = 1 ∧ xP * xP⁻¹ = 1 ∧ xR * xR⁻¹ = 1` suffices_by (
        strip_tac >> irule EQ_TRANS >>
        qexists_tac `xtp * xtb * xp * xb * (xZ * xZ⁻¹) * (xP * xP⁻¹) * (xR * xR⁻¹)` >>
        REVERSE CONJ_TAC >- simp[] >> rpt $ pop_assum kall_tac >>
        metis_tac[mul_assoc,mul_comm]) >>
    rw[] >> irule mul_rinv_pos >> UNABBREV_ALL_TAC >> fs[valid_dist_gen_funs_def] >> simp[lt_le]
QED

Theorem in_measurable_borel_tsan_importance_ratio:
    ∀n (m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space) d0 P Z R bet phi.
        measure_space m_s ∧ measure_space m_o ∧ measure_space m_a ∧ measure_space m_r ∧
        valid_dist_gen_funs m_s m_o m_a m_r d0 P Z R bet ∧
        valid_dist_gen_funs m_s m_o m_a m_r d0 P Z R phi ∧
        (∀w a. w ∈ m_space m_o ∧ a ∈ m_space m_a ∧ bet w a = 0 ⇒ phi w a = 0) ⇒
        importance_ratio phi bet ∈ Borel_measurable (traj_sig_alg_n n m_s m_o m_a m_r)
Proof
    rpt gen_tac >> DISCH_TAC >> fs[valid_dist_gen_funs_def] >> gvs[] >>
    `∀n. sigma_algebra (traj_sig_alg_n n m_s m_o m_a m_r)` by simp[sigma_algebra_traj_sig_alg_n] >>
    Induct_on `n` >> rw[]
    >- (irule IN_MEASURABLE_BOREL_CONG >> qexists_tac `λx. 1` >> simp[IN_MEASURABLE_BOREL_CONST'] >>
        qx_gen_tac `h` >> Cases_on `h` >> simp[in_traj_m_space_n,importance_ratio_def]) >>
    map_every (fn (pos,tm,qex,ths) => irule_at pos tm >> qexistsl_tac qex >> simp ths) [
        (Any,IN_MEASURABLE_BOREL_CONG,
            [`λh. importance_ratio phi bet (t_traj h) * phi (t_obs h) (t_act h) * (bet (t_obs h) (t_act h))⁻¹`],[]),
        (Any,IN_MEASURABLE_BOREL_MUL',[`λh. phi (t_obs h) (t_act h) * (bet (t_obs h) (t_act h))⁻¹`,
            `importance_ratio phi bet ∘ t_traj`],[mul_assoc]),
        (Pos hd,INST_TYPE [``:β`` |-> ``:α``] IN_MEASURABLE_BOREL_COMP,
            [`t_traj`,`importance_ratio phi bet`,`traj_sig_alg_n n m_s m_o m_a m_r`],[]),
        (Pos (el 2),INST_TYPE [``:α`` |-> ``:(α,ρ,σ,ω) traj``,``:β`` |-> ``:ω # α``] IN_MEASURABLE_BOREL_COMP,
            [`λh. (t_obs h,t_act h)`,`λ(w,a). phi w a * (bet w a)⁻¹`,`sig_alg (m_o × m_a)`],
            [sig_alg_prod_measure_space]),
        (Pos (el 3),IN_MEASURABLE_PROD_SIGMA,[`t_act`,`t_obs`],[]),
        (Pos (el 4),IN_MEASURABLE_BOREL_MUL_INV,[`λ(w,a). bet w a`,`λ(w,a). phi w a`],
            [Ntimes (GSYM sig_alg_prod_measure_space) 2,IN_SPACE_PROD_SIGMA,PAIR_FUN2]),
        (Any,SIGMA_ALGEBRA_PROD_SIGMA_WEAK,[],[])] >>
    simp[traj_obs_measurable,traj_action_measurable,traj_traj_measurable] >> qx_gen_tac `h` >> Cases_on `h` >>
    simp[in_traj_m_space_n,importance_ratio_def,traj_obs_def,traj_action_def,traj_traj_def]
QED

Definition traj_return_def:
    traj_return g (init s) = 0 ∧
    traj_return g (tcons (h: (α,extreal,σ,ω) traj) w a s r) = traj_return g h + (g pow (num_steps h)) * r
End

Theorem in_measurable_borel_tsan_traj_return:
    ∀n (m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: extreal m_space) g.
        measure_space m_s ∧ measure_space m_o ∧ measure_space m_a ∧ measure_space m_r ∧
        sig_alg m_r = Borel ⇒ traj_return g ∈ Borel_measurable (traj_sig_alg_n n m_s m_o m_a m_r)
Proof
    rpt gen_tac >> DISCH_TAC >> fs[] >>
    `∀n. sigma_algebra (traj_sig_alg_n n m_s m_o m_a m_r)` by simp[sigma_algebra_traj_sig_alg_n] >>
    Induct_on `n` >> rw[]
    >- (irule IN_MEASURABLE_BOREL_CONG >> qexists_tac `λx. 0` >> simp[IN_MEASURABLE_BOREL_CONST'] >>
        qx_gen_tac `h` >> Cases_on `h` >> simp[in_traj_m_space_n,traj_return_def]) >>
    map_every (fn (pos,tm,qex,ths) => irule_at pos tm >> qexistsl_tac qex >> simp ths) [
        (Any,IN_MEASURABLE_BOREL_CONG,
            [`λh. traj_return g (t_traj h) + g pow num_steps (t_traj h) * t_rew h`],[]),
        (Any,IN_MEASURABLE_BOREL_ADD',
            [`λh. g pow num_steps (t_traj h) * t_rew h`,`λh. traj_return g (t_traj h)`],[]),
        (Pos hd,INST_TYPE [``:β`` |-> ``:α``] IN_MEASURABLE_BOREL_COMP,
            [`t_traj`,`traj_return g`,`traj_sig_alg_n n m_s m_o m_a m_r`],[]),
        (Any,IN_MEASURABLE_BOREL_MUL',[`t_rew`,`λh. g pow num_steps (t_traj h)`],[]),
        (Pos hd,INST_TYPE [``:β`` |-> ``:α``] IN_MEASURABLE_BOREL_COMP,
            [`t_traj`,`λh. g pow num_steps h`,`traj_sig_alg_n n m_s m_o m_a m_r`],[SF CONJ_ss]),
        (Pos hd,IN_MEASURABLE_BOREL_POW_EXP,[`num_steps`,`λh. g`],
            [IN_MEASURABLE_BOREL_CONST',num_steps_measurable])] >>
    qpat_x_assum `_ = _` $ SUBST1_TAC o SYM >> simp[traj_reward_measurable,traj_traj_measurable] >>
    qx_gen_tac `h` >> Cases_on `h` >> fs[in_traj_m_space_n] >> simp[traj_return_def,traj_traj_def,traj_reward_def]
QED

Definition traj_ret_cdf_def:
    traj_ret_cdf n m_s m_o m_a m_r d0 P Z R bet g c = prob
        (density (traj_measure_space_n n m_s m_o m_a m_r) (traj_pdf d0 P Z R bet))
        ({h:(α,extreal,σ,ω) traj | traj_return g h ≤ c} ∩ (traj_m_space_n n m_s m_o m_a m_r))
End

Theorem opeis_pos_fn:
    ∀n (m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space) d0 P Z R bet phi f.
        sigma_finite_measure_space m_s ∧ sigma_finite_measure_space m_o ∧
        sigma_finite_measure_space m_a ∧ sigma_finite_measure_space m_r ∧
        valid_dist_gen_funs m_s m_o m_a m_r d0 P Z R bet ∧
        valid_dist_gen_funs m_s m_o m_a m_r d0 P Z R phi ∧
        (∀w a. w ∈ m_space m_o ∧ a ∈ m_space m_a ∧ bet w a = 0 ⇒ phi w a = 0) ∧
        f ∈ Borel_measurable (traj_sig_alg_n n m_s m_o m_a m_r) ∧
        (∀x. x ∈ traj_m_space_n n m_s m_o m_a m_r ⇒ 0 ≤ f x) ⇒
        ∫⁺ (density (traj_measure_space_n n m_s m_o m_a m_r) (traj_pdf d0 P Z R phi)) f =
        ∫⁺ (density (traj_measure_space_n n m_s m_o m_a m_r) (traj_pdf d0 P Z R bet))
        (λh. traj_pdf d0 P Z R phi h * (traj_pdf d0 P Z R bet h)⁻¹ * f h)
Proof
    rw[] >> irule rn_derivative_density_change_pos >>
    simp[traj_pdf_n_pos,in_measurable_borel_tsan_traj_pdf,measure_space_traj_measure_space_n,SF SFY_ss] >>
    qspecl_then [`traj_measure_space_n n m_s m_o m_a m_r`,`λx. traj_pdf d0 P Z R bet x ≠ +∞`]
        (irule_at Any o SIMP_RULE (srw_ss ()) []) FORALL_IMP_AE >>
    simp[traj_pdf_n_not_infty,measure_space_traj_measure_space_n,SF SFY_ss] >>
    rw[] >> dxrule_all_then assume_tac traj_pdf_n_abs_cont >> simp[]
QED

Theorem opeis:
    ∀n (m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space) d0 P Z R bet phi f.
        sigma_finite_measure_space m_s ∧ sigma_finite_measure_space m_o ∧
        sigma_finite_measure_space m_a ∧ sigma_finite_measure_space m_r ∧
        valid_dist_gen_funs m_s m_o m_a m_r d0 P Z R bet ∧
        valid_dist_gen_funs m_s m_o m_a m_r d0 P Z R phi ∧
        (∀w a. w ∈ m_space m_o ∧ a ∈ m_space m_a ∧ bet w a = 0 ⇒ phi w a = 0) ∧
        f ∈ Borel_measurable (traj_sig_alg_n n m_s m_o m_a m_r) ⇒
        ∫ (density (traj_measure_space_n n m_s m_o m_a m_r) (traj_pdf d0 P Z R phi)) f =
        ∫ (density (traj_measure_space_n n m_s m_o m_a m_r) (traj_pdf d0 P Z R bet))
        (λh. traj_pdf d0 P Z R phi h * (traj_pdf d0 P Z R bet h)⁻¹ * f h)
Proof
    rw[integral_def] >> `∀x1:extreal x2 x3 x4. x1 = x3 ∧ x2 = x4 ⇒ x1 - x2 = x3 - x4` by simp[] >>
    pop_assum irule >> NTAC 2 $ resolve_then (Pos $ el 1) (irule_at $ Pos last) opeis_pos_fn EQ_TRANS >>
    qexistsl_tac [`bet`,`bet`] >> NTAC 2 $ resolve_then Any (irule_at Any) pos_fn_integral_cong EQ_SYM >>
    csimp[iffLR IN_MEASURABLE_BOREL_PLUS_MINUS,FN_PLUS_POS,FN_MINUS_POS] >>
    irule_at Any measure_space_density >>
    simp[traj_pdf_n_pos,in_measurable_borel_tsan_traj_pdf,measure_space_traj_measure_space_n,SF SFY_ss] >>
    simp[GSYM FORALL_IMP_CONJ_THM] >> qx_gen_tac `h` >> DISCH_TAC >>
    `0 ≤ traj_pdf d0 P Z R phi h * (traj_pdf d0 P Z R bet h)⁻¹` by (
        Cases_on `traj_pdf d0 P Z R bet h = 0` >- (drule_all_then mp_tac traj_pdf_n_abs_cont >> simp[]) >>
        irule le_mul >> irule_at Any le_inv >> simp[lt_le,traj_pdf_n_pos,SF SFY_ss]) >>
    simp[le_mul,FN_PLUS_POS,FN_MINUS_POS] >>
    map_every (drule_then (mp_tac o Q.SPEC `f`) o cj 1 o INST_TYPE [``:α`` |-> ``:(α,ρ,σ,ω) traj``])
        [FN_PLUS_CMUL_full,FN_MINUS_CMUL_full] >>
    simp[FUN_EQ_THM,fn_plus_def,fn_minus_def]
QED

Theorem opeis_integrable:
    ∀n (m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space) d0 P Z R bet phi f.
        sigma_finite_measure_space m_s ∧ sigma_finite_measure_space m_o ∧
        sigma_finite_measure_space m_a ∧ sigma_finite_measure_space m_r ∧
        valid_dist_gen_funs m_s m_o m_a m_r d0 P Z R bet ∧
        valid_dist_gen_funs m_s m_o m_a m_r d0 P Z R phi ∧
        (∀w a. w ∈ m_space m_o ∧ a ∈ m_space m_a ∧ bet w a = 0 ⇒ phi w a = 0) ∧
        integrable (density (traj_measure_space_n n m_s m_o m_a m_r) (traj_pdf d0 P Z R phi)) f ⇒
        integrable (density (traj_measure_space_n n m_s m_o m_a m_r) (traj_pdf d0 P Z R bet))
        (λh. traj_pdf d0 P Z R phi h * (traj_pdf d0 P Z R bet h)⁻¹ * f h)
Proof
    rw[] >> fs[integrable_def] >> `∀x:extreal y z. x = y ∧ x ≠ z ⇒ y ≠ z` by simp[] >>
    pop_assum $ NTAC 2 o pop_assum o C (resolve_then Any (irule_at $ Pos last)) >>
    irule_at Any IN_MEASURABLE_BOREL_MUL' >>
    qexistsl_tac [`f`,`λh. traj_pdf d0 P Z R phi h * (traj_pdf d0 P Z R bet h)⁻¹`] >> simp[] >>
    NTAC 2 $ resolve_then (Pos $ el 1) (irule_at $ Pos last) opeis_pos_fn EQ_TRANS >>
    qexistsl_tac [`bet`,`bet`] >> NTAC 2 $ resolve_then Any (irule_at Any) pos_fn_integral_cong EQ_SYM >>
    csimp[iffLR IN_MEASURABLE_BOREL_PLUS_MINUS,FN_PLUS_POS,FN_MINUS_POS] >>
    irule_at Any IN_MEASURABLE_BOREL_MUL_INV >> irule_at Any measure_space_density >>
    qexistsl_tac [`traj_pdf d0 P Z R bet`,`traj_pdf d0 P Z R phi`] >>
    simp[traj_pdf_n_pos,in_measurable_borel_tsan_traj_pdf,measure_space_traj_measure_space_n,
        sigma_algebra_traj_sig_alg_n,SF SFY_ss] >>
    CONJ_TAC >- (rw[] >> drule_all_then mp_tac traj_pdf_n_abs_cont >> simp[]) >>
    simp[GSYM FORALL_IMP_CONJ_THM] >> qx_gen_tac `h` >> DISCH_TAC >>
    `0 ≤ traj_pdf d0 P Z R phi h * (traj_pdf d0 P Z R bet h)⁻¹` by (
        Cases_on `traj_pdf d0 P Z R bet h = 0` >- (drule_all_then mp_tac traj_pdf_n_abs_cont >> simp[]) >>
        irule le_mul >> irule_at Any le_inv >> simp[lt_le,traj_pdf_n_pos,SF SFY_ss]) >>
    simp[le_mul,FN_PLUS_POS,FN_MINUS_POS] >>
    map_every (drule_then (mp_tac o Q.SPEC `f`) o cj 1 o INST_TYPE [``:α`` |-> ``:(α,ρ,σ,ω) traj``])
        [FN_PLUS_CMUL_full,FN_MINUS_CMUL_full] >>
    simp[FUN_EQ_THM,fn_plus_def,fn_minus_def]
QED

Theorem opeis_traj_ret_cdf:
    ∀n (m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: extreal m_space) d0 P Z R bet phi g c.
        sigma_finite_measure_space m_s ∧ sigma_finite_measure_space m_o ∧
        sigma_finite_measure_space m_a ∧ sigma_finite_measure_space m_r ∧
        sig_alg m_r = Borel ∧ valid_dist_gen_funs m_s m_o m_a m_r d0 P Z R bet ∧
        valid_dist_gen_funs m_s m_o m_a m_r d0 P Z R phi ∧
        (∀w a. w ∈ m_space m_o ∧ a ∈ m_space m_a ∧ bet w a = 0 ⇒ phi w a = 0) ⇒
        traj_ret_cdf n m_s m_o m_a m_r d0 P Z R phi g c = integral
        (density (traj_measure_space_n n m_s m_o m_a m_r) (traj_pdf d0 P Z R bet))
        (λh. traj_pdf d0 P Z R phi h * (traj_pdf d0 P Z R bet h)⁻¹ * 𝟙 {h | traj_return g h ≤ c} h)
Proof
    rw[traj_ret_cdf_def,prob_def] >>
    `measure_space (traj_measure_space_n n m_s m_o m_a m_r)` by simp[measure_space_traj_measure_space_n] >>
    fs[sigma_finite_measure_space_def] >> NTAC 4 $ qpat_x_assum `sigma_finite _` kall_tac >>
    `traj_pdf d0 P Z R bet ∈ Borel_measurable (traj_sig_alg_n n m_s m_o m_a m_r) ∧
      traj_pdf d0 P Z R phi ∈ Borel_measurable (traj_sig_alg_n n m_s m_o m_a m_r)`
        by simp[in_measurable_borel_tsan_traj_pdf] >>
    qmatch_abbrev_tac `measure dmp hs = _ dmb f` >>
    `measure_space dmb ∧ measure_space dmp` by (qunabbrevl_tac [`dmb`,`dmp`] >>
        NTAC 2 $ irule_at Any measure_space_density >> simp[traj_pdf_n_pos,SF SFY_ss]) >>
    `hs ∈ measurable_sets dmp` by (qunabbrevl_tac [`hs`,`dmp`] >>
        `traj_return g ∈ Borel_measurable (traj_sig_alg_n n m_s m_o m_a m_r)`
            by simp[in_measurable_borel_tsan_traj_return] >>
         dxrule_then mp_tac IN_MEASURABLE_BOREL_RC >> simp[]) >>
    drule_all_then (SUBST1_TAC o SYM) integral_indicator >>
    `𝟙 hs ∈ Borel_measurable (sig_alg dmp)` by (irule IN_MEASURABLE_BOREL_INDICATOR >>
        simp[] >> qexists_tac `hs` >> simp[]) >>
    irule EQ_TRANS >>
    qexists_tac `∫ dmb (λh. traj_pdf d0 P Z R phi h * (traj_pdf d0 P Z R bet h)⁻¹ * 𝟙 hs h)` >>
    irule_at Any integral_cong >> simp[] >> CONJ_TAC
    >- (UNABBREV_ALL_TAC >> simp[INDICATOR_FN_INTER,indicator_fn_def]) >>
    qunabbrevl_tac [`dmb`,`dmp`] >> irule EQ_SYM >>
    irule $ SIMP_RULE (srw_ss ()) [expectation_def] importance_sampling_rn_derivative >> fs[] >>
    qspecl_then [`traj_measure_space_n n m_s m_o m_a m_r`,`λx. traj_pdf d0 P Z R bet x ≠ +∞`]
        (irule_at Any o SIMP_RULE (srw_ss ()) []) FORALL_IMP_AE >>
    simp[traj_pdf_n_pos,traj_pdf_n_not_infty,SF SFY_ss] >> rw[] >>
    dxrule_all_then assume_tac traj_pdf_n_abs_cont >> simp[]
QED

Theorem opeir_pos_fn:
    ∀n (m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space) d0 P Z R bet phi f.
        sigma_finite_measure_space m_s ∧ sigma_finite_measure_space m_o ∧
        sigma_finite_measure_space m_a ∧ sigma_finite_measure_space m_r ∧
        valid_dist_gen_funs m_s m_o m_a m_r d0 P Z R bet ∧
        valid_dist_gen_funs m_s m_o m_a m_r d0 P Z R phi ∧
        (∀w a. w ∈ m_space m_o ∧ a ∈ m_space m_a ∧ bet w a = 0 ⇒ phi w a = 0) ∧
        f ∈ Borel_measurable (traj_sig_alg_n n m_s m_o m_a m_r) ∧
        (∀x. x ∈ traj_m_space_n n m_s m_o m_a m_r ⇒ 0 ≤ f x) ⇒
        ∫⁺ (density (traj_measure_space_n n m_s m_o m_a m_r) (traj_pdf d0 P Z R phi)) f =
        ∫⁺ (density (traj_measure_space_n n m_s m_o m_a m_r) (traj_pdf d0 P Z R bet))
        (λh. importance_ratio phi bet h * f h)
Proof
    rw[] >> drule_all_then SUBST1_TAC opeis_pos_fn >> irule pos_fn_integral_density_cong >>
    simp[importance_ratio_n_valid,measure_space_traj_measure_space_n,traj_pdf_n_pos,SF SFY_ss] >>
    map_every (fn (pos,th,qex,ths) => irule_at pos th >> qexistsl_tac qex >> csimp ths) [
        (Pos (el 5),IN_MEASURABLE_BOREL_MUL',[`f`,`importance_ratio phi bet`],[]),
        (Pos (el 6),IN_MEASURABLE_BOREL_MUL',[`f`,`λh. traj_pdf d0 P Z R phi h * (traj_pdf d0 P Z R bet h)⁻¹`],[]),
        (Pos (el 1),IN_MEASURABLE_BOREL_MUL_INV,[`traj_pdf d0 P Z R bet`,`traj_pdf d0 P Z R phi`],[])] >>
    simp[sigma_algebra_traj_sig_alg_n,in_measurable_borel_tsan_traj_pdf,
        in_measurable_borel_tsan_importance_ratio,SF SFY_ss] >>
    simp[Once $ GSYM AND_IMP_INTRO,GSYM FORALL_IMP_CONJ_THM] >> qx_gen_tac `h` >> DISCH_TAC >>
    CONJ_ASM1_TAC >- (rw[] >> drule_all_then assume_tac traj_pdf_n_abs_cont >> simp[]) >>
    NTAC 2 $ irule_at (Pos last) le_mul >> simp[] >> drule_all_then assume_tac traj_ir_n_pos >> simp[] >>
    Cases_on `traj_pdf d0 P Z R bet h = 0` >> simp[] >> irule le_mul >>
    irule_at Any le_inv >> simp[lt_le,traj_pdf_n_pos,traj_pdf_n_not_infty,SF SFY_ss]
QED

Theorem opeir:
    ∀n (m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space) d0 P Z R bet phi f.
        sigma_finite_measure_space m_s ∧ sigma_finite_measure_space m_o ∧
        sigma_finite_measure_space m_a ∧ sigma_finite_measure_space m_r ∧
        valid_dist_gen_funs m_s m_o m_a m_r d0 P Z R bet ∧
        valid_dist_gen_funs m_s m_o m_a m_r d0 P Z R phi ∧
        (∀w a. w ∈ m_space m_o ∧ a ∈ m_space m_a ∧ bet w a = 0 ⇒ phi w a = 0) ∧
        f ∈ Borel_measurable (traj_sig_alg_n n m_s m_o m_a m_r) ⇒
        ∫ (density (traj_measure_space_n n m_s m_o m_a m_r) (traj_pdf d0 P Z R phi)) f =
        ∫ (density (traj_measure_space_n n m_s m_o m_a m_r) (traj_pdf d0 P Z R bet))
        (λh. importance_ratio phi bet h * f h)
Proof
    rw[integral_def] >> `∀x1:extreal x2 x3 x4. x1 = x3 ∧ x2 = x4 ⇒ x1 - x2 = x3 - x4` by simp[] >>
    pop_assum irule >> NTAC 2 $ resolve_then (Pos $ el 1) (irule_at $ Pos last) opeir_pos_fn EQ_TRANS >>
    qexistsl_tac [`bet`,`bet`] >> NTAC 2 $ resolve_then Any (irule_at Any) pos_fn_integral_cong EQ_SYM >>
    csimp[iffLR IN_MEASURABLE_BOREL_PLUS_MINUS,FN_PLUS_POS,FN_MINUS_POS] >>
    irule_at Any measure_space_density >>
    simp[traj_pdf_n_pos,in_measurable_borel_tsan_traj_pdf,measure_space_traj_measure_space_n,SF SFY_ss] >>
    simp[GSYM FORALL_IMP_CONJ_THM] >> qx_gen_tac `h` >> DISCH_TAC >>
    `0 ≤ importance_ratio phi bet h` by (drule_all_then mp_tac traj_ir_n_pos >> simp[]) >>
    simp[le_mul,FN_PLUS_POS,FN_MINUS_POS] >>
    map_every (drule_then (mp_tac o Q.SPEC `f`) o cj 1 o INST_TYPE [``:α`` |-> ``:(α,ρ,σ,ω) traj``])
        [FN_PLUS_CMUL_full,FN_MINUS_CMUL_full] >>
    simp[FUN_EQ_THM,fn_plus_def,fn_minus_def]
QED

Theorem opeir_integrable:
    ∀n (m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space) d0 P Z R bet phi f.
        sigma_finite_measure_space m_s ∧ sigma_finite_measure_space m_o ∧
        sigma_finite_measure_space m_a ∧ sigma_finite_measure_space m_r ∧
        valid_dist_gen_funs m_s m_o m_a m_r d0 P Z R bet ∧
        valid_dist_gen_funs m_s m_o m_a m_r d0 P Z R phi ∧
        (∀w a. w ∈ m_space m_o ∧ a ∈ m_space m_a ∧ bet w a = 0 ⇒ phi w a = 0) ∧
        integrable (density (traj_measure_space_n n m_s m_o m_a m_r) (traj_pdf d0 P Z R phi)) f ⇒
        integrable (density (traj_measure_space_n n m_s m_o m_a m_r) (traj_pdf d0 P Z R bet))
        (λh. importance_ratio phi bet h * f h)
Proof
    rw[] >> fs[integrable_def] >> `∀x:extreal y z. x = y ∧ x ≠ z ⇒ y ≠ z` by simp[] >>
    pop_assum $ NTAC 2 o pop_assum o C (resolve_then Any (irule_at $ Pos last)) >>
    irule_at Any IN_MEASURABLE_BOREL_MUL' >> qexistsl_tac [`f`,`importance_ratio phi bet`] >>
    simp[sigma_algebra_traj_sig_alg_n,in_measurable_borel_tsan_importance_ratio,SF SFY_ss] >>
    NTAC 2 $ resolve_then (Pos $ el 1) (irule_at $ Pos last) opeir_pos_fn EQ_TRANS >>
    qexistsl_tac [`bet`,`bet`] >> NTAC 2 $ resolve_then Any (irule_at Any) pos_fn_integral_cong EQ_SYM >>
    csimp[iffLR IN_MEASURABLE_BOREL_PLUS_MINUS,FN_PLUS_POS,FN_MINUS_POS] >>
    irule_at Any measure_space_density >>
    simp[traj_pdf_n_pos,in_measurable_borel_tsan_traj_pdf,measure_space_traj_measure_space_n,SF SFY_ss] >>
    simp[GSYM FORALL_IMP_CONJ_THM] >> qx_gen_tac `h` >> DISCH_TAC >>
    `0 ≤ importance_ratio phi bet h` by (drule_all_then mp_tac traj_ir_n_pos >> simp[]) >>
    simp[le_mul,FN_PLUS_POS,FN_MINUS_POS] >>
    map_every (drule_then (mp_tac o Q.SPEC `f`) o cj 1 o INST_TYPE [``:α`` |-> ``:(α,ρ,σ,ω) traj``])
        [FN_PLUS_CMUL_full,FN_MINUS_CMUL_full] >>
    simp[FUN_EQ_THM,fn_plus_def,fn_minus_def]
QED

Theorem opeir_traj_ret_cdf:
    ∀n (m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: extreal m_space) d0 P Z R bet phi g c.
        sigma_finite_measure_space m_s ∧ sigma_finite_measure_space m_o ∧
        sigma_finite_measure_space m_a ∧ sigma_finite_measure_space m_r ∧
        sig_alg m_r = Borel ∧ valid_dist_gen_funs m_s m_o m_a m_r d0 P Z R bet ∧
        valid_dist_gen_funs m_s m_o m_a m_r d0 P Z R phi ∧
        (∀w a. w ∈ m_space m_o ∧ a ∈ m_space m_a ∧ bet w a = 0 ⇒ phi w a = 0) ⇒
        traj_ret_cdf n m_s m_o m_a m_r d0 P Z R phi g c = integral
        (density (traj_measure_space_n n m_s m_o m_a m_r) (traj_pdf d0 P Z R bet))
        (λh. importance_ratio phi bet h * 𝟙 {h | traj_return g h ≤ c} h)
Proof
    rw[] >>
    qspecl_then [`n`,`m_s`,`m_o`,`m_a`,`m_r`,`d0`,`P`,`Z`,`R`,`bet`,`phi`,`g`,`c`]
        assume_tac opeis_traj_ret_cdf >>
    rfs[] >> pop_assum kall_tac >>
    `measure_space (traj_measure_space_n n m_s m_o m_a m_r)` by simp[measure_space_traj_measure_space_n] >>
    fs[sigma_finite_measure_space_def] >> NTAC 4 $ qpat_x_assum `sigma_finite _` kall_tac >>
    `traj_return g ∈ Borel_measurable (traj_sig_alg_n n m_s m_o m_a m_r)`
        by simp[in_measurable_borel_tsan_traj_return] >>
    `traj_pdf d0 P Z R bet ∈ Borel_measurable (traj_sig_alg_n n m_s m_o m_a m_r) ∧
      traj_pdf d0 P Z R phi ∈ Borel_measurable (traj_sig_alg_n n m_s m_o m_a m_r)`
        by simp[in_measurable_borel_tsan_traj_pdf] >>
    `importance_ratio phi bet ∈ Borel_measurable (traj_sig_alg_n n m_s m_o m_a m_r)`
        by simp[in_measurable_borel_tsan_importance_ratio,SF SFY_ss] >>
    `(∀h. h ∈ traj_m_space_n n m_s m_o m_a m_r ⇒ 0 ≤ traj_pdf d0 P Z R bet h) ∧
        (∀h. h ∈ traj_m_space_n n m_s m_o m_a m_r ⇒ 0 ≤ traj_pdf d0 P Z R phi h)` by (
        simp[traj_pdf_n_pos,SF SFY_ss]) >>
    `∀h. h ∈ traj_m_space_n n m_s m_o m_a m_r ⇒ 0 ≤ importance_ratio phi bet h` by (
        rw[] >> dxrule_all_then assume_tac traj_ir_n_pos >> simp[]) >>
    `∀x. x ∈ traj_m_space_n n m_s m_o m_a m_r ∧ traj_pdf d0 P Z R bet x = 0 ⇒ traj_pdf d0 P Z R phi x = 0` by (
        rw[] >> dxrule_all_then assume_tac traj_pdf_n_abs_cont >> simp[]) >>
    qmatch_abbrev_tac `(_ (density m f) gis):extreal = (_ _ gir)` >>
    `∫ (density m f) gis = ∫⁺ (density m f) gis ∧ ∫ (density m f) gir = ∫⁺ (density m f) gir ∧
        ∫⁺ (density m f) gis = ∫⁺ (density m f) gir` suffices_by simp[] >>
    irule_at Any pos_fn_integral_density_cong >> NTAC 2 $ irule_at Any integral_pos_fn >>
    irule_at Any measure_space_density >> simp[] >> UNABBREV_ALL_TAC >>
    csimp[INDICATOR_FN_POS,le_mul] >>
    map_every (fn (pos,th,qex,ths) => irule_at pos th >> qexistsl_tac qex >> csimp ths) [
        (Pos (el 1),IN_MEASURABLE_BOREL_MUL',
            [`𝟙 {h | traj_return g h ≤ c}`,`λh. traj_pdf d0 P Z R phi h * (traj_pdf d0 P Z R bet h)⁻¹`],[]),
        (Pos (el 4),IN_MEASURABLE_BOREL_MUL',[`𝟙 {h | traj_return g h ≤ c}`,`importance_ratio phi bet`],[]),
        (Pos (el 3),IN_MEASURABLE_BOREL_INDICATOR,
            [`{h | traj_return g h ≤ c} ∩ space (traj_sig_alg_n n m_s m_o m_a m_r)`],
            [Excl "space_traj_sig_alg",Excl "subsets_traj_sig_alg"]),
        (Any,IN_MEASURABLE_BOREL_RC,[],[]),
        (Any,IN_MEASURABLE_BOREL_MUL',
            [`λh. (traj_pdf d0 P Z R bet h)⁻¹ * 𝟙 {h | traj_pdf d0 P Z R bet h ≠ 0} h`,`traj_pdf d0 P Z R phi`],[]),
        (Any,IN_MEASURABLE_BOREL_INV,[`traj_pdf d0 P Z R bet`],
            [GSYM sig_alg_traj_measure_space,Excl "sig_alg_traj_measure_space"])] >>
    rw[] >- (rw[indicator_fn_def] >> fs[]) >- (rw[indicator_fn_def])
    >- (irule le_mul >> simp[INDICATOR_FN_POS] >> Cases_on `traj_pdf d0 P Z R bet x = 0` >> fs[] >>
        irule le_mul >> simp[] >> simp[le_lt] >> DISJ1_TAC >> simp[indicator_fn_def] >>
        irule inv_pos' >> simp[lt_le,traj_pdf_n_not_infty,SF SFY_ss])
    >- (rw[indicator_fn_def] >> irule importance_ratio_valid >> simp[] >>
        qexistsl_tac [`m_a`,`m_o`,`m_r`,`m_s`] >> simp[] >>
        simp[SIMP_RULE (srw_ss ()) [SUBSET_DEF] traj_m_space_n_subset_traj_m_space,SF SFY_ss])
QED

(*****************)
(*** Histories ***)
(*****************)

Datatype:
    hist = hnil | hcons hist ω α ρ
End

Definition num_hsteps_def:
    num_hsteps hnil = 0 ∧
    num_hsteps (hcons (h: (α,ρ,ω) hist) w a r) = SUC (num_hsteps h)
End

Definition hist_n_gen_def:
    hist_n_gen 0 (og: ω) (ag: α) (rg: ρ) = hnil ∧
    hist_n_gen (SUC n) og ag rg = hcons (hist_n_gen n og ag rg) og ag rg
End

Definition hist_cross_def:
    (hist_cross hnil hnil ⇔ T) ∧
    (hist_cross hnil (hcons (h: (α,ρ,ω) hist) w a r) ⇔ F) ∧
    (hist_cross (hcons hs ws as rs) hnil ⇔ F) ∧
    (hist_cross (hcons hs ws as rs) (hcons h w a r) ⇔
        w ∈ ws ∧ a ∈ as ∧ r ∈ rs ∧ hist_cross hs h)
End

Theorem in_hist_cross:
    (hnil:((α,ρ,ω) hist) ∈ hist_cross hnil ⇔ T) ∧
    (∀(h: (α,ρ,ω) hist) w a r. hcons h w a r ∉ hist_cross hnil) ∧
    (∀hs ws as rs. hnil:((α,ρ,ω) hist) ∉ hist_cross (hcons hs ws as rs)) ∧
    (∀hs ws as rs (h: (α,ρ,ω) hist) w a r. hcons h w a r ∈ hist_cross (hcons hs ws as rs) ⇔
        w ∈ ws ∧ a ∈ as ∧ r ∈ rs ∧ h ∈ hist_cross hs)
Proof
    simp[GSYM FORALL_AND_THM,RIGHT_AND_FORALL_THM] >> rpt gen_tac >>
    `∀(h: (α,ρ,ω) hist) hs. h ∈ hist_cross hs ⇔ hist_cross hs h` by simp[IN_APP] >>
    simp[hist_cross_def]
QED

Theorem hist_cross_empty:
    (hist_cross hnil ≠ (∅ : (α,ρ,ω) hist -> bool)) ∧
    (∀hs ws as rs. hist_cross (hcons hs ws as rs) = (∅ : (α,ρ,ω) hist -> bool) ⇔
        ws = ∅ ∨ as = ∅ ∨ rs = ∅ ∨ hist_cross hs = ∅)
Proof
    rw[] >- (simp[GSYM MEMBER_NOT_EMPTY] >> qexists_tac `hnil` >> simp[in_hist_cross]) >>
    eq_tac >> CONV_TAC CONTRAPOS_CONV >> simp[GSYM MEMBER_NOT_EMPTY] >> DISCH_TAC >> fs[]
    >- (rename [`hist_cross (hcons hs ws as rs)`,
            `w ∈ ws`,`a ∈ as`,` r ∈ rs`,`h ∈ hist_cross hs`] >>
        qexists_tac `hcons h w a r` >> simp[in_hist_cross])
    >- (rename [`h ∈ _`] >> Cases_on `h` >> fs[in_hist_cross] >> simp[SF SFY_ss])
QED

Theorem hist_cross_eq:
    ∀hs gs. hist_cross hs = hist_cross gs ⇔ hs = gs ∨
        (hist_cross hs = (∅ : (α,ρ,ω) hist -> bool) ∧ hist_cross gs = ∅)
Proof
    rw[] >> eq_tac >> rw[] >> fs[] >> Cases_on `hist_cross gs = ∅` >> simp[] >>
    last_x_assum mp_tac >> qid_spec_tac `hs` >> Induct_on `gs` >> rw[] >> Cases_on `hs` >> simp[]
    >- (fs[GSYM MEMBER_NOT_EMPTY] >> rename [`h ∈ _`] >> pop_assum mp_tac >> simp[EXTENSION] >>
        qexists_tac `h` >> simp[] >> Cases_on `h` >> fs[in_hist_cross])
    >- (fs[GSYM MEMBER_NOT_EMPTY] >> rename [`h ∈ _`] >> pop_assum mp_tac >> simp[EXTENSION] >>
        qexists_tac `h` >> simp[] >> Cases_on `h` >> fs[in_hist_cross])
    >- (rename [`hist_cross (hcons hs hws has hrs) = hist_cross (hcons gs gws gas grs)`] >>
        fs[EXTENSION] >> last_x_assum $ irule_at Any >> rename [`h ∈ _`] >>
        first_assum $ drule_then assume_tac o iffRL >> Cases_on `h` >- fs[in_hist_cross] >>
        rename [`hcons h w a r`] >> fs[in_hist_cross] >> qexists_tac `h` >> simp[] >>
        rpt CONJ_TAC >> qx_gen_tac `v`
        >| let fun fv tm = first_x_assum $ qspec_then tm assume_tac in [fv `hcons v w a r`,
            fv `hcons h v a r`,fv `hcons h w v r`,fv `hcons h w a v`] end >>
        rfs[in_hist_cross])
QED

Definition hist_m_space_n_def:
    hist_m_space_n n (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space) =
        hist_cross (hist_n_gen n (m_space m_o) (m_space m_a) (m_space m_r))
End

Theorem in_hist_m_space_n:
    (∀m_o m_a m_r. (hnil: (α,ρ,ω) hist) ∈ hist_m_space_n 0 m_o m_a m_r) ∧
    (∀n m_o m_a m_r. (hnil: (α,ρ,ω) hist) ∉ hist_m_space_n (SUC n) m_o m_a m_r) ∧
    (∀m_o m_a m_r (h: (α,ρ,ω) hist) w a r. (hcons h w a r) ∉ hist_m_space_n 0 m_o m_a m_r) ∧
    (∀n m_o m_a m_r (h: (α,ρ,ω) hist) w a r. (hcons h w a r) ∈ hist_m_space_n (SUC n) m_o m_a m_r ⇔
        w ∈ m_space m_o ∧ a ∈ m_space m_a ∧ r ∈ m_space m_r ∧ h ∈ hist_m_space_n n m_o m_a m_r)
Proof
    simp[GSYM FORALL_AND_THM,RIGHT_AND_FORALL_THM] >> rpt gen_tac >>
    `∀(h: (α,ρ,ω) hist) n m_o m_a m_r. h ∈ hist_m_space_n n m_o m_a m_r ⇔
        hist_m_space_n n m_o m_a m_r h` by simp[IN_APP] >>
    simp[hist_m_space_n_def] >> pop_assum kall_tac >> rpt CONJ_TAC >> TRY (eq_tac >> DISCH_TAC) >>
    fs[hist_n_gen_def,hist_cross_def]
QED

Definition hist_rect_sets_n_def:
    hist_rect_sets_n n (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space) =
        IMAGE hist_cross (hist_cross (hist_n_gen n
            (measurable_sets m_o) (measurable_sets m_a) (measurable_sets m_r)))
End

Theorem in_hist_rect_sets_n:
    (∀(m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space) hs.
        hs ∈ hist_rect_sets_n 0 m_o m_a m_r ⇔ hs = hist_cross hnil) ∧
    (∀n (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space) gs.
        gs ∈ hist_rect_sets_n (SUC n) m_o m_a m_r ⇔
        ∃hs ws as rs. gs = hist_cross (hcons hs ws as rs) ∧
        ws ∈ measurable_sets m_o ∧ as ∈ measurable_sets m_a ∧
        rs ∈ measurable_sets m_r ∧ hist_cross hs ∈ hist_rect_sets_n n m_o m_a m_r)
Proof
    CONJ_ASM1_TAC
    >- (rw[hist_rect_sets_n_def] >> eq_tac >> DISCH_TAC
        >- (gvs[hist_n_gen_def] >> rename [`h ∈ _`] >> Cases_on `h` >> fs[in_hist_cross])
        >- (gvs[] >> qexists_tac `hnil` >> simp[hist_n_gen_def,in_hist_cross])) >>
    Induct_on `n` >| [all_tac,pop_assum $ assume_tac o GSYM] >>
    rw[] >> gvs[hist_rect_sets_n_def] >> eq_tac >> DISCH_TAC
    >- (gvs[] >> rename [`h ∈ _`] >> Cases_on `h` >>
        FULL_SIMP_TAC pure_ss [ONE,hist_n_gen_def,in_hist_cross] >> rename [`hcons hs ws as rs`] >>
        qexistsl_tac [`hs`,`ws`,`as`,`rs`] >> simp[] >> last_x_assum $ irule o iffLR >>
        qexists_tac `hs` >> simp[])
    >- (gvs[] >> fs[hist_n_gen_def] >> qexists_tac `hcons hs ws as rs` >> simp[] >>
        ASM_SIMP_TAC bool_ss [ONE,hist_n_gen_def,in_hist_cross] >>
        Cases_on `hs` >> fs[in_hist_cross,hist_cross_eq,hist_cross_empty])
    >- (last_x_assum kall_tac >> gvs[] >> rename [`h ∈ _`] >> pop_assum mp_tac >> Cases_on `h` >>
        simp[Once hist_n_gen_def,in_hist_cross] >> rw[] >> rename [`hcons hs ws as rs`] >>
        qexistsl_tac [`hs`,`ws`,`as`,`rs`] >> simp[] >> qexists_tac `hs` >> simp[])
    >- (last_x_assum kall_tac >> pop_assum mp_tac >> simp[Once hist_n_gen_def] >> DISCH_TAC >>
        gvs[] >> rename [`hist_cross hs = hist_cross fs`] >> Cases_on `fs` >> fs[in_hist_cross] >>
        rename [`_ = hist_cross (hcons hsh hsw hsa hsr)`] >>
        last_x_assum $ qspecl_then [`m_o`,`m_a`,`m_r`,`hsh`]
            assume_tac o SIMP_RULE (srw_ss ()) [GSYM LEFT_FORALL_IMP_THM,GSYM RIGHT_EXISTS_AND_THM] o iffLR >>
        pop_assum $ qspecl_then [`hsw`,`hsa`,`hsr`,`hsh`] assume_tac >>
        rfs[] >> rename [`hist_cross (hcons _ _ _ _) = hist_cross gs`] >> fs[] >>
        qexists_tac `hcons gs ws as rs` >> simp[Once hist_n_gen_def,in_hist_cross] >>
        pop_assum kall_tac >> gvs[hist_cross_eq,in_hist_cross] >> simp[hist_cross_empty])
QED

Definition hist_measurable_sets_n_def:
    hist_measurable_sets_n n (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space) =
        subsets (sigma (hist_m_space_n n m_o m_a m_r) (hist_rect_sets_n n m_o m_a m_r))
End

Theorem hist_rect_set_n_measurable:
    ∀n (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space).
        hist_rect_sets_n n m_o m_a m_r ⊆ hist_measurable_sets_n n m_o m_a m_r
Proof
    simp[hist_measurable_sets_n_def,SIGMA_SUBSET_SUBSETS]
QED

Theorem subset_class_hist_rect_sets_n:
    ∀n (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space). subset_class (m_space m_o) (measurable_sets m_o) ∧
        subset_class (m_space m_a) (measurable_sets m_a) ∧ subset_class (m_space m_r) (measurable_sets m_r) ⇒
        subset_class (hist_m_space_n n m_o m_a m_r) (hist_rect_sets_n n m_o m_a m_r)
Proof
    rw[] >> Induct_on `n` >> fs[subset_class_def] >> simp[in_hist_rect_sets_n] >> rw[] >>
    rpt $ first_x_assum $ dxrule_then assume_tac >> simp[SUBSET_DEF] >> qx_gen_tac `h` >>
    Cases_on `h` >> simp[in_hist_cross,in_hist_m_space_n] >> fs[SUBSET_DEF]
QED

Theorem hist_m_space_n_rect_set:
    ∀n (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space).
        measure_space m_o ∧ measure_space m_a ∧ measure_space m_r ⇒
        hist_m_space_n n m_o m_a m_r ∈ hist_rect_sets_n n m_o m_a m_r
Proof
    rw[] >> Induct_on `n` >> fs[in_hist_rect_sets_n,hist_m_space_n_def,hist_n_gen_def] >>
    qexistsl_tac [`hist_n_gen n (m_space m_o) (m_space m_a) (m_space m_r)`,
            `m_space m_o`,`m_space m_a`,`m_space m_r`] >>
    simp[MEASURE_SPACE_SPACE]
QED

Definition hstep_cross_def:
    (hstep_cross hs ws as rs hnil ⇔ F) ∧
    (hstep_cross hs ws as rs (hcons (h: (α,ρ,ω) hist) w a r) ⇔
        w ∈ ws ∧ a ∈ as ∧ r ∈ rs ∧ h ∈ hs)
End

Theorem in_hstep_cross:
    (∀hs ws as rs. hnil:((α,ρ,ω) hist) ∉ hstep_cross hs ws as rs) ∧
    (∀hs ws as rs (h: (α,ρ,ω) hist) w a r. hcons h w a r ∈ hstep_cross hs ws as rs ⇔
        w ∈ ws ∧ a ∈ as ∧ r ∈ rs ∧ h ∈ hs)
Proof
    simp[GSYM FORALL_AND_THM,RIGHT_AND_FORALL_THM] >> rpt gen_tac >> simp[IN_APP,hstep_cross_def]
QED

Definition hstep_rect_sets_n_def:
    hstep_rect_sets_n 0 (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space) =
        IMAGE hist_cross (hist_cross hnil) ∧
    hstep_rect_sets_n (SUC n) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space) =
        {hstep_cross hs ws as rs | hs ∈ hist_measurable_sets_n n m_o m_a m_r ∧
        ws ∈ measurable_sets m_o ∧ as ∈ measurable_sets m_a ∧ rs ∈ measurable_sets m_r}
End

Theorem in_hstep_rect_sets_n:
    (∀(m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space) hs.
        hs ∈ hstep_rect_sets_n 0 m_o m_a m_r ⇔ hs = hist_cross hnil) ∧
    (∀n (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space) gs.
        gs ∈ hstep_rect_sets_n (SUC n) m_o m_a m_r ⇔
        ∃hs ws as rs. gs = hstep_cross hs ws as rs ∧
        hs ∈ hist_measurable_sets_n n m_o m_a m_r ∧ ws ∈ measurable_sets m_o ∧
        as ∈ measurable_sets m_a ∧ rs ∈ measurable_sets m_r)
Proof
    rw[] >> simp[hstep_rect_sets_n_def] >> eq_tac >> rw[]
    >- (rename [`hr ∈ _`] >> Cases_on `hr` >> fs[in_hist_cross])
    >- (qexists_tac `hnil` >> simp[in_hist_cross])
QED

Theorem hist_rect_sets_n_subset_hstep_rect_sets_n:
    ∀n (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space).
        hist_rect_sets_n n m_o m_a m_r ⊆ hstep_rect_sets_n n m_o m_a m_r
Proof
    rw[] >> simp[SUBSET_DEF] >> Induct_on `n` >>
    simp[hist_rect_sets_n_def,hist_n_gen_def,hstep_rect_sets_n_def] >> qx_gen_tac `h` >> rw[] >>
    rename [`h ∈ _`] >> Cases_on `h` >> fs[in_hist_cross] >> rename [`hcons hs ws as rs`] >>
    qexistsl_tac [`hist_cross hs`,`ws`,`as`,`rs`] >> simp[] >>
    irule_at Any $ SIMP_RULE (srw_ss ()) [SUBSET_DEF] hist_rect_set_n_measurable >>
    simp[hist_rect_sets_n_def,EXTENSION] >> qx_gen_tac `h` >>
    Cases_on `h` >> simp[in_hist_cross,in_hstep_cross]
QED

Theorem hist_cross_hstep_cross:
    ∀hs ws as rs. hist_cross (hcons hs ws as rs): (α,ρ,ω) hist -> bool =
        hstep_cross (hist_cross hs) ws as rs
Proof
    rw[] >> simp[EXTENSION] >> qx_gen_tac `h` >> Cases_on `h` >>
    simp[in_hist_cross,in_hstep_cross]
QED

(* perhaps just subset class reqs, or space in subsets req needed *)
Theorem hstep_rect_set_n_measurable:
    ∀n (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space).
        measure_space m_o ∧ measure_space m_a ∧ measure_space m_r ⇒
        hstep_rect_sets_n n m_o m_a m_r ⊆ hist_measurable_sets_n n m_o m_a m_r
Proof
    rw[] >> simp[SUBSET_DEF] >> Cases_on `n` >> qx_gen_tac `hs` >> rw[hstep_rect_sets_n_def]
    >- (irule $ SIMP_RULE (srw_ss ()) [SUBSET_DEF] hist_rect_set_n_measurable >>
        simp[hist_rect_sets_n_def,hist_n_gen_def]) >>
    rename [`SUC n`,`hstep_cross hs _ _ _ ∈ _`] >> fs[hist_measurable_sets_n_def,sigma_def] >> rw[] >>
    Cases_on `ws = ∅ ∨ as = ∅ ∨ rs = ∅`
    >- (`∅ ∈ P` by fs[sigma_algebra_def,algebra_def] >>
        `hstep_cross hs ws as rs = ∅` suffices_by simp[] >>
        simp[EXTENSION] >> qx_gen_tac `h` >> Cases_on `h` >> simp[in_hstep_cross] >> fs[]) >>
    last_x_assum $ qspec_then `{hs| hstep_cross hs ws as rs ∈ P}` $
        irule o SIMP_RULE (srw_ss ()) [] >>
    REVERSE CONJ_TAC
    >- (simp[SUBSET_DEF] >> qx_gen_tac `hs` >> strip_tac >>
        qpat_x_assum `_ ⊆ _` $ irule_at Any o SIMP_RULE (srw_ss ()) [SUBSET_DEF] >>
        simp[in_hist_rect_sets_n] >> gvs[hist_rect_sets_n_def] >> rename [`hs ∈ _`] >>
        qexistsl_tac [`hs`,`ws`,`as`,`rs`] >> simp[hist_cross_hstep_cross] >>
        qexists_tac `hs` >> simp[]) >>
    rw[SIGMA_ALGEBRA_ALT_DIFF]
    >- (fs[GSYM MEMBER_NOT_EMPTY] >>
        rename [`{hs | hstep_cross hs ws as rs ∈ P}`,`w ∈ ws`,`a ∈ as`,`r ∈ rs`] >>
        dxrule_then assume_tac SIGMA_ALGEBRA_SUBSET_CLASS >> fs[subset_class_def] >> rw[] >>
        first_x_assum $ dxrule_then mp_tac >> rename [`hstep_cross hs _ _ _`] >> simp[SUBSET_DEF] >>
        rw[] >> rename [`h ∈ _`] >> first_x_assum $ qspec_then `hcons h w a r` mp_tac >>
        simp[in_hstep_cross,in_hist_m_space_n])
    (* this is the problem case *)
    >- (qpat_x_assum `_ ⊆ _` $ irule_at Any o SIMP_RULE (srw_ss ()) [SUBSET_DEF] >>
        simp[in_hist_rect_sets_n,hist_m_space_n_def] >>
        qexistsl_tac [`hist_n_gen n (m_space m_o) (m_space m_a) (m_space m_r)`,`ws`,`as`,`rs`] >>
        simp[hist_cross_hstep_cross] >> simp[GSYM hist_m_space_n_def,hist_m_space_n_rect_set])
    >- (dxrule_then mp_tac SIGMA_ALGEBRA_DIFF >> simp[] >>
        DISCH_THEN $ qspecl_then [`hstep_cross t ws as rs`,`hstep_cross s ws as rs`] mp_tac >>
        simp[] >> qmatch_abbrev_tac `hs1 ∈ _ ⇒ hs2 ∈ _` >> `hs1 = hs2` suffices_by simp[] >>
        UNABBREV_ALL_TAC >> simp[EXTENSION] >> qx_gen_tac `h` >> Cases_on `h` >> simp[in_hstep_cross] >>
        eq_tac >> strip_tac >> simp[])
    >- (dxrule_then mp_tac SIGMA_ALGEBRA_COUNTABLE_UNION >> simp[] >>
        DISCH_THEN $ qspec_then `IMAGE (λhs. hstep_cross hs ws as rs) c` mp_tac >>
        `BIGUNION (IMAGE (λhs. hstep_cross hs ws as rs) c) = hstep_cross (BIGUNION c) ws as rs` suffices_by (
            DISCH_THEN SUBST1_TAC >> DISCH_THEN irule >> simp[image_countable] >>
            fs[SUBSET_DEF] >> rw[] >> fs[]) >>
        simp[EXTENSION,IN_BIGUNION_IMAGE] >> qx_gen_tac `h` >> Cases_on `h` >> simp[in_hstep_cross] >>
        eq_tac >> strip_tac >> simp[SF SFY_ss])
QED

Theorem hist_measurable_sets_n_alt:
    ∀n (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space).
        measure_space m_o ∧ measure_space m_a ∧ measure_space m_r ⇒
        hist_measurable_sets_n n m_o m_a m_r =
        subsets (sigma (hist_m_space_n n m_o m_a m_r) (hstep_rect_sets_n n m_o m_a m_r))
Proof
    rw[hist_measurable_sets_n_def] >> irule SUBSET_ANTISYM >> CONJ_TAC
    >- (irule SIGMA_MONOTONE >> simp[hist_rect_sets_n_subset_hstep_rect_sets_n])
    >- (irule SIGMA_BOUNDED >> simp[GSYM hist_measurable_sets_n_def] >>
        simp[hstep_rect_set_n_measurable])
QED

Definition hist_sig_alg_n_def:
    hist_sig_alg_n n (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space) =
        (hist_m_space_n n m_o m_a m_r,hist_measurable_sets_n n m_o m_a m_r)
End

Theorem sigma_algebra_hist_sig_alg_n:
    ∀n (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space).
        measure_space m_o ∧ measure_space m_a ∧ measure_space m_r ⇒
        sigma_algebra (hist_sig_alg_n n m_o m_a m_r)
Proof
    rw[hist_sig_alg_n_def,hist_measurable_sets_n_def] >> simp[SIGMA_REDUCE] >>
    irule SIGMA_ALGEBRA_SIGMA >> simp[subset_class_def] >> qid_spec_tac `n` >>
    Induct_on `n` >> rw[in_hist_rect_sets_n] >> simp[SUBSET_DEF] >> qx_gen_tac `h` >>
    Cases_on `h` >> simp[in_hist_cross,in_hist_m_space_n,MEASURE_SPACE_IN_MSPACE,SF SFY_ss] >>
    last_x_assum $ dxrule_then assume_tac >> fs[SUBSET_DEF]
QED

Theorem sigma_algebra_hist_sig_alg_0:
    ∀(m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space).
        sigma_algebra (hist_sig_alg_n 0 m_o m_a m_r)
Proof
    rw[hist_sig_alg_n_def,hist_measurable_sets_n_def,SIGMA_REDUCE] >>
    irule SIGMA_ALGEBRA_SIGMA >> rw[subset_class_def,SUBSET_DEF] >> rename[`h ∈ hs`,`h ∈ _`,`hs ∈ _`] >>
    gvs[hist_rect_sets_n_def,hist_n_gen_def] >> rename [`hist_cross hr`] >>
    Cases_on `hr` >> fs[in_hist_cross] >> Cases_on `h` >> fs[in_hist_cross,in_hist_m_space_n]
QED

Definition hist_measure_rec_lex_def:
    hist_measure_rec_lex (INL (n,_)) = (n,0) ∧
    hist_measure_rec_lex (INR (n,_)) = (n,SUC 0)
End

Definition hist_measure_rec_def:
    hist_measure_n 0 (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space) = C 𝟙 hnil ∧
    hist_measure_n (SUC n) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space) = (λhs.
        ∫⁺ (hist_measure_space_n n m_o m_a m_r) (λh.
        ∫⁺ m_o (λw. ∫⁺ m_a (λa. ∫⁺ m_r (λr. 𝟙 hs (hcons h w a r)))))) ∧
    hist_measure_space_n n (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space) =
        (hist_m_space_n n m_o m_a m_r,hist_measurable_sets_n n m_o m_a m_r,hist_measure_n n m_o m_a m_r)
Termination
    WF_REL_TAC `inv_image ($< LEX $<) hist_measure_rec_lex` >> simp[hist_measure_rec_lex_def]
End

Theorem hist_measure_n_def:
    (∀(m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space).
        hist_measure_n 0 m_o m_a m_r = C 𝟙 hnil) ∧
    (∀n (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space).
        hist_measure_n (SUC n) m_o m_a m_r = (λhs. ∫⁺ (hist_measure_space_n n m_o m_a m_r) (λh.
        ∫⁺ m_o (λw. ∫⁺ m_a (λa. ∫⁺ m_r (λr. 𝟙 hs (hcons h w a r)))))))
Proof
    simp[hist_measure_rec_def]
QED

Theorem hist_measure_space_n_def:
    ∀n (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space).
        hist_measure_space_n n m_o m_a m_r =
        (hist_m_space_n n m_o m_a m_r,hist_measurable_sets_n n m_o m_a m_r,hist_measure_n n m_o m_a m_r)
Proof
    simp[hist_measure_rec_def]
QED

Theorem m_space_hist_measure_space:
    ∀n (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space).
        m_space (hist_measure_space_n n m_o m_a m_r) = hist_m_space_n n m_o m_a m_r
Proof
    simp[hist_measure_space_n_def]
QED

Theorem measurable_sets_hist_measure_space:
    ∀n (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space).
        measurable_sets (hist_measure_space_n n m_o m_a m_r) = hist_measurable_sets_n n m_o m_a m_r
Proof
    simp[hist_measure_space_n_def]
QED

Theorem measure_hist_measure_space:
    ∀n (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space).
        measure (hist_measure_space_n n m_o m_a m_r) = hist_measure_n n m_o m_a m_r
Proof
    simp[hist_measure_space_n_def]
QED

Theorem sig_alg_hist_measure_space:
    ∀n (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space).
        sig_alg (hist_measure_space_n n m_o m_a m_r) = hist_sig_alg_n n m_o m_a m_r
Proof
    simp[hist_measure_space_n_def,hist_sig_alg_n_def]
QED

Theorem space_hist_sig_alg:
    ∀n (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space).
        space (hist_sig_alg_n n m_o m_a m_r) = hist_m_space_n n m_o m_a m_r
Proof
    simp[hist_sig_alg_n_def]
QED

Theorem subsets_hist_sig_alg:
    ∀n (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space).
        subsets (hist_sig_alg_n n m_o m_a m_r) = hist_measurable_sets_n n m_o m_a m_r
Proof
    simp[hist_sig_alg_n_def]
QED

val HIST_ss = named_rewrites_with_names "HIST" $ map name_to_thname [
    "m_space_hist_measure_space","measurable_sets_hist_measure_space","measure_hist_measure_space",
    "sig_alg_hist_measure_space","space_hist_sig_alg","subsets_hist_sig_alg"];

val _ = augment_srw_ss [HIST_ss];

Theorem subset_class_hstep_rect_sets_n:
    ∀n (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space).
        measure_space m_o ∧ measure_space m_a ∧ measure_space m_r ⇒
        subset_class (hist_m_space_n n m_o m_a m_r) (hstep_rect_sets_n n m_o m_a m_r)
Proof
    rw[] >> `sigma_algebra (hist_sig_alg_n n m_o m_a m_r)` by simp[sigma_algebra_hist_sig_alg_n] >>
    `hstep_rect_sets_n n m_o m_a m_r ⊆ hist_measurable_sets_n n m_o m_a m_r` by
        simp[hstep_rect_set_n_measurable] >>
    dxrule_then mp_tac SIGMA_ALGEBRA_SUBSET_CLASS >> fs[SUBSET_DEF] >> simp[subset_class_def]
QED

Theorem in_measure_preserving_hcons:
    ∀n (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space).
        sigma_finite_measure_space m_o ∧ sigma_finite_measure_space m_a ∧ sigma_finite_measure_space m_r ∧
        sigma_finite_measure_space (hist_measure_space_n n m_o m_a m_r) ⇒
        (λ(h,w,a,r). hcons h w a r) ∈ measure_preserving
        (hist_measure_space_n n m_o m_a m_r × m_o × m_a × m_r) (hist_measure_space_n (SUC n) m_o m_a m_r)
Proof
    REVERSE $ rw[in_measure_preserving]
    >- (rename [`hs ∈ _`] >> qmatch_abbrev_tac `_ (m_h × _ × _ × _) _ = _` >> simp[hist_measure_n_def] >>
        `sigma_finite_measure_space (m_a × m_r) ∧ sigma_finite_measure_space (m_o × m_a × m_r)` by
            simp[sigma_finite_measure_space_prod_measure] >>
        map_every (fn tm => drule_all_then mp_tac measure_prod_measure_space_itr >>
            qpat_x_assum `_ ∈ _` kall_tac >> simp[] >> DISCH_TAC >> irule IRULER >> simp[FUN_EQ_THM] >>
            qx_gen_tac tm >> pop_assum $ qspec_then tm assume_tac o cj 2) [`h`,`w`,`a`] >>
        simp[GSYM pos_fn_integral_indicator] >> irule IRULER >>
        simp[FUN_EQ_THM] >> qx_gen_tac `r` >> simp[indicator_fn_def,EXISTS_PROD]) >>
    pop_assum kall_tac >> fs[sigma_finite_measure_space_def] >> NTAC 3 $ qpat_x_assum `sigma_finite _` kall_tac >>
    `BIJ (λ(h,w,a,r). hcons h w a r) (m_space (hist_measure_space_n n m_o m_a m_r × m_o × m_a × m_r))
      (hist_m_space_n (SUC n) m_o m_a m_r)` by (
        simp[m_space_prod_measure_space,hist_m_space_n_def,hist_n_gen_def] >>
        simp[BIJ_ALT,EXISTS_UNIQUE_ALT,EXISTS_PROD,FORALL_PROD,FUNSET,in_hist_cross] >>
        qx_gen_tac `h` >> Cases_on `h` >> simp[in_hist_cross] >> rename [`w ∈ _ ∧ a ∈ _ ∧ r ∈ _ ∧ h ∈ _`] >>
        rw[] >> qexistsl_tac [`h`,`w`,`a`,`r`] >> rw[] >> eq_tac >> rw[] >> simp[]) >>
    `∀hs ws as rs. (hstep_cross hs ws as rs): (α,ρ,ω) hist -> bool = 
      IMAGE (λ(h,w,a,r). hcons h w a r) (hs × ws × as × rs)` by (rw[] >>
        simp[EXTENSION,EXISTS_PROD] >> qx_gen_tac `h` >> Cases_on `h` >> simp[in_hstep_cross] >>
        (* redifinition of step_cross? *)
        eq_tac >> strip_tac >> simp[]) >>
    simp[in_measurability_preserving_alt,sigma_algebra_hist_sig_alg_n] >>
    qexistsl_tac [`prod_sets (hist_measurable_sets_n n m_o m_a m_r)
        (prod_sets (measurable_sets m_o) (prod_sets (measurable_sets m_a) (measurable_sets m_r)))`,
        `hstep_rect_sets_n (SUC n) m_o m_a m_r`] >> rw[]
    >- (NTAC 2 $ pop_assum kall_tac >>
        `sigma_algebra (hist_sig_alg_n n m_o m_a m_r)` by simp[sigma_algebra_hist_sig_alg_n] >>
        map_every imp_res_tac
            [MEASURE_SPACE_SPACE,SIGMA_ALGEBRA_SPACE,MEASURE_SPACE_SUBSET_CLASS,SIGMA_ALGEBRA_SUBSET_CLASS] >>
        NTAC 4 $ last_x_assum kall_tac >> fs[] >> simp[m_space_prod_measure_space,sig_alg_prod_measure_space] >>
        qspecl_then [`sig_alg m_a`,`sig_alg m_r`] SUBST1_TAC prod_sigma_def >> simp[] >>
        map_every (fn tms => qspecl_then tms mp_tac SIGMA_PROD_ITR >> simp[Excl "IN_PROD_SETS"] >>
                strip_tac >> pop_assum kall_tac >> rename [`subset_class sp sts`]) [
            [`sig_alg m_o`,`sig_alg m_a`,`sig_alg m_r`],[`hist_sig_alg_n n m_o m_a m_r`,`sig_alg m_o`,`sp,sts`]])
    >- simp[hist_sig_alg_n_def,hist_measurable_sets_n_alt,SIGMA_REDUCE]
    >- (simp[m_space_prod_measure_space,prod_sets_def,subset_class_def,GSYM RIGHT_EXISTS_AND_THM] >>
        rw[] >> qspecl_then [`n`,`m_o`,`m_a`,`m_r`] mp_tac sigma_algebra_hist_sig_alg_n >>
        simp[] >> strip_tac >> dxrule_then mp_tac SIGMA_ALGEBRA_SUBSET_CLASS >> simp[subset_class_def] >>
        strip_tac >> NTAC 3 $ irule_at Any SUBSET_CROSS >> simp[MEASURABLE_SETS_SUBSET_SPACE])
    >- simp[MEASURE_SPACE_SUBSET_CLASS,subset_class_hstep_rect_sets_n]
    >- (rename [`hs × ws × as × rs`] >> simp[in_hstep_rect_sets_n] >>
        qexistsl_tac [`hs`,`ws`,`as`,`rs`] >> simp[])
    >- (simp[GSYM RIGHT_EXISTS_AND_THM] >> gvs[in_hstep_rect_sets_n] >>
        qexistsl_tac [`hs`,`ws`,`as`,`rs`] >> simp[] >> dxrule_then irule BIJ_PREIMAGE_IMAGE >>
        simp[m_space_prod_measure_space] >> NTAC 3 $ irule_at Any SUBSET_CROSS >>
        simp[MEASURABLE_SETS_SUBSET_SPACE] >>
        qspecl_then [`n`,`m_o`,`m_a`,`m_r`] mp_tac sigma_algebra_hist_sig_alg_n >>
        simp[] >> strip_tac >> dxrule_then mp_tac SIGMA_ALGEBRA_SUBSET_CLASS >> simp[subset_class_def])
QED

Theorem hist_measure_space_n_iso:
    ∀n (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space). sigma_finite_measure_space m_o ∧
        sigma_finite_measure_space m_a ∧ sigma_finite_measure_space m_r ∧
        sigma_finite_measure_space (hist_measure_space_n n m_o m_a m_r) ⇒
        isomorphic (hist_measure_space_n (SUC n) m_o m_a m_r)
        (hist_measure_space_n n m_o m_a m_r × m_o × m_a × m_r)
Proof
    rw[] >> irule isomorphic_sym_imp >> simp[isomorphic_def] >>
    qexists_tac `λ(h,w,a,r). hcons h w a r` >> simp[in_measure_preserving_hcons]
QED

Theorem sigma_finite_measure_space_hist_measure_space_n:
    ∀n (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space). sigma_finite_measure_space m_o ∧
        sigma_finite_measure_space m_a ∧ sigma_finite_measure_space m_r ⇒
        sigma_finite_measure_space (hist_measure_space_n n m_o m_a m_r)
Proof
    rw[] >> Induct_on `n`
    >- (simp[hist_measure_space_n_def,hist_measure_n_def] >>
        qspec_then `hist_sig_alg_n 0 m_o m_a m_r` mp_tac sigma_finite_measure_space_fixed_state_measure >>
        fs[sigma_finite_measure_space_def] >> simp[sigma_algebra_hist_sig_alg_n])
    >- (irule $ INST_TYPE [``:α`` |-> ``:(α,ρ,ω) hist # ω # α # ρ``] sigma_finite_measure_space_isomorphic >>
        qexists_tac `hist_measure_space_n n m_o m_a m_r × m_o × m_a × m_r` >>
        irule_at Any isomorphic_sym_imp >> simp[hist_measure_space_n_iso] >>
        NTAC 3 (irule sigma_finite_measure_space_prod_measure >> simp[]))
QED

Theorem in_measure_preserving_hcons:
    ∀n (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space). sigma_finite_measure_space m_o ∧
        sigma_finite_measure_space m_a ∧ sigma_finite_measure_space m_r ⇒
        (λ(h,w,a,r). hcons h w a r) ∈ measure_preserving
        (hist_measure_space_n n m_o m_a m_r × m_o × m_a × m_r) (hist_measure_space_n (SUC n) m_o m_a m_r)
Proof
    rw[] >> irule in_measure_preserving_hcons >> simp[sigma_finite_measure_space_hist_measure_space_n]
QED

Theorem hist_measure_space_n_iso:
    ∀n (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space). sigma_finite_measure_space m_o ∧
        sigma_finite_measure_space m_a ∧ sigma_finite_measure_space m_r ⇒
        isomorphic (hist_measure_space_n (SUC n) m_o m_a m_r)
        (hist_measure_space_n n m_o m_a m_r × m_o × m_a × m_r)
Proof
    rw[] >> irule hist_measure_space_n_iso >> simp[sigma_finite_measure_space_hist_measure_space_n]
QED

Theorem measure_space_hist_measure_space_n:
    ∀n (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space). sigma_finite_measure_space m_o ∧
        sigma_finite_measure_space m_a ∧ sigma_finite_measure_space m_r ⇒
        measure_space (hist_measure_space_n n m_o m_a m_r)
Proof
    rw[] >> irule sigma_finite_measure_space_measure_space >>
    simp[sigma_finite_measure_space_hist_measure_space_n]
QED

Theorem measure_space_hist_measure_space_0:
    ∀(m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space).
        measure_space (hist_measure_space_n 0 m_o m_a m_r)
Proof
    rw[hist_measure_space_n_def,hist_measure_n_def] >>
    resolve_then Any (irule o SIMP_RULE (srw_ss ()) [])
        sigma_algebra_hist_sig_alg_0 measure_space_fixed_state_measure
QED

Theorem sigma_finite_measure_space_hist_measure_space_0:
    ∀(m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space).
        sigma_finite_measure_space (hist_measure_space_n 0 m_o m_a m_r)
Proof
    rw[hist_measure_space_n_def,hist_measure_n_def] >>
    resolve_then Any (irule o SIMP_RULE (srw_ss ()) [])
        sigma_algebra_hist_sig_alg_0 sigma_finite_measure_space_fixed_state_measure
QED

Theorem hist_tonelli_0:
    ∀(m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space) f.
        (∀h. h ∈ hist_m_space_n 0 m_o m_a m_r ⇒ 0 ≤ f h) ∧
        f ∈ Borel_measurable (hist_sig_alg_n 0 m_o m_a m_r) ⇒
        ∫⁺ (hist_measure_space_n 0 m_o m_a m_r) f = f hnil
Proof
    rw[] >> simp[hist_measure_space_n_def,hist_measure_n_def] >>
    dxrule_at Any pos_fn_integral_fixed_state_measure >> simp[] >> DISCH_THEN irule >>
    simp[sigma_algebra_hist_sig_alg_0,in_hist_m_space_n]
QED

Theorem hist_tonelli_SUC:
    ∀n (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space) f.
        sigma_finite_measure_space m_o ∧ sigma_finite_measure_space m_a ∧ sigma_finite_measure_space m_r ∧
        (∀h. h ∈ hist_m_space_n (SUC n) m_o m_a m_r ⇒ 0 ≤ f h) ∧
        f ∈ Borel_measurable (hist_sig_alg_n (SUC n) m_o m_a m_r) ⇒
        ∫⁺ (hist_measure_space_n (SUC n) m_o m_a m_r) f = ∫⁺ (hist_measure_space_n n m_o m_a m_r) (λh.
        ∫⁺ m_o (λw. ∫⁺ m_a (λa. ∫⁺ m_r (λr. f (hcons h w a r)))))
Proof
    rw[] >> irule EQ_TRANS >>
    qexists_tac `∫⁺ (hist_measure_space_n n m_o m_a m_r × m_o × m_a × m_r)
        (f ∘ (λ(h,w,a,r). hcons h w a r))` >>
    irule_at Any iso_pos_fn_integral_comp >> simp[in_measure_preserving_hcons] >>
    irule_at (Pos (el 1)) $ INST_TYPE [``:α`` |-> ``:(α,ρ,ω) hist``,
        ``:β`` |-> ``:(α,ρ,ω) hist # ω # α # ρ``] measure_space_isomorphic >>
    qexists_tac `(hist_measure_space_n (SUC n) m_o m_a m_r)` >>
    csimp[hist_measure_space_n_iso,measure_space_hist_measure_space_n] >>
    `∀h w a r. h ∈ hist_m_space_n n m_o m_a m_r ∧ w ∈ m_space m_o ∧
      a ∈ m_space m_a ∧ r ∈ m_space m_r ⇒ 0 ≤ f (hcons h w a r)` by (rw[] >>
        first_x_assum irule >> simp[in_hist_m_space_n]) >>
    qpat_x_assum `∀h. _ ⇒ 0 ≤ f h` kall_tac >>
    `sigma_finite_measure_space (m_a × m_r) ∧ sigma_finite_measure_space (m_o × m_a × m_r)`
        by simp[sigma_finite_measure_space_prod_measure] >>
    `sigma_finite_measure_space (hist_measure_space_n n m_o m_a m_r)`
        by simp[sigma_finite_measure_space_hist_measure_space_n] >>
    `(λ(h,w,a,r). hcons h w a r) ∈ measurable
      (sig_alg ((hist_measure_space_n n m_o m_a m_r × m_o × m_a × m_r)))
      (hist_sig_alg_n (SUC n) m_o m_a m_r)` by (irule measurability_preserving_measurable >>
        qspecl_then [`n`,`m_o`,`m_a`,`m_r`] mp_tac in_measure_preserving_hcons >>
        simp[in_measure_preserving]) >>
    dxrule_all_then assume_tac MEASURABLE_COMP >>
    `(f ∘ (λ(h,w,a,r). hcons h w a r)) = (λ(h,w,a,r). f (hcons h w a r))` by simp[FUN_EQ_THM,UNCURRY] >>
    pop_assum SUBST_ALL_TAC >> fs[Once sig_alg_prod_measure_space,Excl "sig_alg_hist_measure_space"] >>
    dxrule_at_then (Pos (el 3)) (fn th => assume_tac (cj 2 th) >> assume_tac (cj 6 th)) TONELLI_ALT >>
    rfs[FORALL_PROD,in_mspace_prod_measure_space] >> pop_assum kall_tac >>
    NTAC 2 (irule_at Any pos_fn_integral_cong >> csimp[GSYM FORALL_IMP_CONJ_THM] >> gen_tac >> DISCH_TAC >>
        first_x_assum $ drule_then assume_tac >> fs[Once sig_alg_prod_measure_space] >>
        dxrule_at_then (Pos (el 3)) (fn th => assume_tac (cj 2 th) >> assume_tac (cj 6 th)) TONELLI_ALT >>
        rfs[FORALL_PROD,in_mspace_prod_measure_space] >> pop_assum kall_tac >> irule_at Any pos_fn_integral_pos) >>
    rw[] >> irule_at Any pos_fn_integral_pos >> simp[]
QED

Theorem hist_tonelli_SUC_step:
    ∀n (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space) f.
        sigma_finite_measure_space m_o ∧ sigma_finite_measure_space m_a ∧ sigma_finite_measure_space m_r ∧
        (∀h. h ∈ hist_m_space_n (SUC n) m_o m_a m_r ⇒ 0 ≤ f h) ∧
        f ∈ Borel_measurable (hist_sig_alg_n (SUC n) m_o m_a m_r) ⇒
        ∫⁺ (hist_measure_space_n (SUC n) m_o m_a m_r) f = ∫⁺ (hist_measure_space_n n m_o m_a m_r) (λh.
        ∫⁺ (m_o × m_a × m_r) (λ(w,a,r). f (hcons h w a r)))
Proof
    rw[] >> irule EQ_TRANS >>
    qexists_tac `∫⁺ (hist_measure_space_n n m_o m_a m_r × m_o × m_a × m_r)
        (f ∘ (λ(h,w,a,r). hcons h w a r))` >>
    irule_at Any iso_pos_fn_integral_comp >> simp[in_measure_preserving_hcons] >>
    irule_at (Pos (el 1)) $ INST_TYPE [``:α`` |-> ``:(α,ρ,ω) hist``,
        ``:β`` |-> ``:(α,ρ,ω) hist # ω # α # ρ``] measure_space_isomorphic >>
    qexists_tac `(hist_measure_space_n (SUC n) m_o m_a m_r)` >>
    csimp[hist_measure_space_n_iso,measure_space_hist_measure_space_n] >>
    `(f ∘ (λ(h,w,a,r). hcons h w a r)) = (λ(h,w,a,r). f (hcons h w a r))` by simp[FUN_EQ_THM,UNCURRY] >>
    pop_assum SUBST_ALL_TAC >>
    qspecl_then [`hist_measure_space_n n m_o m_a m_r`,`m_o × m_a × m_r`,
        `(λ(h,w,a,r). f (hcons h w a r))`] (assume_tac) $ cj 6 TONELLI_ALT >>
    `∀x. (λy. (λ(h,w,a,r). f (hcons h w a r)) (x,y)) = (λ(w,a,r). f (hcons x w a r))`
        by simp[FUN_EQ_THM,UNCURRY] >>
    fs[] >> pop_assum kall_tac >> pop_assum irule >>
    simp[sigma_finite_measure_space_hist_measure_space_n,sigma_finite_measure_space_prod_measure] >>
    first_assum $ C (resolve_then (Pos $ el 3) (irule_at Any)) IN_MEASURABLE_BOREL_COMP >>
    qexists_tac `(λ(h,w,a,r). hcons h w a r)` >>
    simp[sig_alg_prod_measure_space,SPACE_PROD_SIGMA,FORALL_PROD,m_space_prod_measure_space] >>
    rpt (irule_at Any SIGMA_ALGEBRA_PROD_SIGMA_WEAK) >> simp[sigma_algebra_hist_sig_alg_n] >>
    resolve_then Any (irule_at Any o SIMP_RULE (srw_ss ()) [sig_alg_prod_measure_space])
        in_measure_preserving_hcons measure_preserving_measurable >>
    rw[] >> first_x_assum irule >> simp[in_hist_m_space_n]
QED

Theorem hist_lst_tonelli_0:
    ∀(m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space) f.
        sigma_finite_measure_space m_s ∧
        (∀h s. h ∈ hist_m_space_n 0 m_o m_a m_r ∧ s ∈ m_space m_s ⇒ 0 ≤ f (h,s)) ∧
        f ∈ Borel_measurable (hist_sig_alg_n 0 m_o m_a m_r × sig_alg m_s) ⇒
        ∫⁺ (hist_measure_space_n 0 m_o m_a m_r × m_s) f = ∫⁺ m_s (λs. f (hnil,s))
Proof
    rw[] >> fs[GSYM sig_alg_hist_measure_space,Excl "sig_alg_hist_measure_space"] >>
    map_every (fn n => drule_at_then Any assume_tac $ cj n TONELLI_ALT) [6,3] >>
    rfs[sigma_finite_measure_space_hist_measure_space_0,FORALL_PROD] >>
    dxrule_at Any hist_tonelli_0 >> simp[] >> DISCH_THEN irule >>
    rw[] >> irule pos_fn_integral_pos >> simp[]
QED

Theorem hist_lst_tonelli_SUC:
    ∀n (m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space) f.
        sigma_finite_measure_space m_s ∧ sigma_finite_measure_space m_o ∧
        sigma_finite_measure_space m_a ∧ sigma_finite_measure_space m_r ∧
        (∀h s. h ∈ hist_m_space_n (SUC n) m_o m_a m_r ∧ s ∈ m_space m_s ⇒ 0 ≤ f (h,s)) ∧
        f ∈ Borel_measurable (hist_sig_alg_n (SUC n) m_o m_a m_r × sig_alg m_s) ⇒
        ∫⁺ (hist_measure_space_n (SUC n) m_o m_a m_r × m_s) f =
        ∫⁺ (hist_measure_space_n n m_o m_a m_r) (λh.
        ∫⁺ m_o (λw. ∫⁺ m_a (λa. ∫⁺ m_s (λs. ∫⁺ m_r (λr. f (hcons h w a r,s))))))
Proof
    rw[] >> fs[GSYM sig_alg_hist_measure_space,Excl "sig_alg_hist_measure_space"] >>
    map_every (fn n => drule_at_then Any assume_tac $ cj n TONELLI_ALT) [3,6] >>
    rfs[sigma_finite_measure_space_hist_measure_space_n,FORALL_PROD] >> pop_assum kall_tac >>
    `∀h. h ∈ hist_m_space_n (SUC n) m_o m_a m_r ⇒ 0 ≤ (λx. ∫⁺ m_s (λy. f (x,y))) h` by (
        rw[] >> irule pos_fn_integral_pos >> simp[]) >>
    drule_all_then SUBST1_TAC hist_tonelli_SUC >> NTAC 2 $ pop_assum kall_tac >>
    irule pos_fn_integral_cong >> csimp[measure_space_hist_measure_space_n,GSYM FORALL_IMP_CONJ_THM] >>
    NTAC 2 (gen_tac >> DISCH_TAC >> irule_at Any pos_fn_integral_pos >>
        irule_at Any pos_fn_integral_cong >> csimp[GSYM FORALL_IMP_CONJ_THM]) >>
    gen_tac >> DISCH_TAC >> rename [`hcons h w a`] >>
    map_every (fn (pos,tm,qex,ths) => irule_at pos tm >> qexistsl_tac qex >> simp ths) [
        (Any,EQ_TRANS,[`∫⁺ (m_r × m_s) (λ(r,s). f (hcons h w a r,s))`],[]),
        (Pos $ el 2,EQ_SYM,[],[SF CONJ_ss]),
        (Pos $ el 2,EQ_SYM,[],[]),
        (Pos $ el 2,EQ_SYM,[],[]),
        (Any,pos_fn_integral_pos,[],[FORALL_PROD,m_space_prod_measure_space]),
        (Any,measure_space_prod_measure,[],[]),
        (Any,SIMP_RULE (srw_ss ()) [] $ Q.SPECL [`m_r`,`m_s`,`(λ(r,s). f (hcons h (w:ω) (a:α) r,s))`] $
            INST_TYPE [``:α`` |-> ``:ρ``,``:β`` |-> ``:σ``] $ cj 5 TONELLI_ALT,[],[]),
        (Any,SIMP_RULE (srw_ss ()) [] $ Q.SPECL [`m_r`,`m_s`,`(λ(r,s). f (hcons h (w:ω) (a:α) r,s))`] $
            INST_TYPE [``:α`` |-> ``:ρ``,``:β`` |-> ``:σ``] $ cj 6 TONELLI_ALT,[],[FORALL_PROD,SF CONJ_ss])] >>
    REVERSE CONJ_TAC >- (rw[] >> first_x_assum irule >> simp[in_hist_m_space_n]) >>
    `(λ(h,w,a,r,s). f (hcons h w a r,s)) ∈ Borel_measurable
      (hist_sig_alg_n n m_o m_a m_r × sig_alg m_o × sig_alg m_a × sig_alg m_r × sig_alg m_s)` by (
        `sigma_algebra (hist_sig_alg_n n m_o m_a m_r × sig_alg m_o × sig_alg m_a ×
          sig_alg m_r × sig_alg m_s)` by (
            rpt (irule_at Any SIGMA_ALGEBRA_PROD_SIGMA_WEAK) >> simp[sigma_algebra_hist_sig_alg_n]) >>
        first_x_assum $ C (resolve_then (Pos $ el 3) irule) IN_MEASURABLE_BOREL_COMP >>
        irule_at Any SIGMA_ALGEBRA_PROD_SIGMA_WEAK >> simp[sigma_algebra_hist_sig_alg_n] >>
        qexists_tac `λ(h,w,a,r,s). (hcons h w a r,s)` >> simp[FORALL_PROD,in_mspace_prod_measure_space] >>
        rpt (irule_at Any SIGMA_ALGEBRA_PROD_SIGMA_WEAK) >> simp[sigma_algebra_hist_sig_alg_n] >>
        irule MEASURABLE_PROD_SIGMA' >> simp[o_DEF,LAMBDA_PROD] >>
        resolve_then (Pos $ el 2) (resolve_then Any
            (irule_at Any o SIMP_RULE (srw_ss ()) [sigma_algebra_hist_sig_alg_n])
            in_measure_preserving_hcons) measure_preserving_measurable IN_MEASURABLE_COMP >>
        qexists_tac `λ(h,w,a,r,s). (h,w,a,r)` >> simp[FORALL_PROD,sig_alg_prod_measure_space] >>
        rpt $ irule_at Any MEASURABLE_PROD_SIGMA' >> simp[o_DEF,LAMBDA_PROD] >>
        dxrule_then assume_tac MEASURABLE_I >>
        NTAC 4 $ pop_assum (fn th => map_every
            (C (resolve_then (Pos $ el 2) (resolve_then Any assume_tac th)) MEASURABLE_COMP)
            [IN_MEASURABLE_FST,IN_MEASURABLE_SND]) >>
        rfs[o_DEF,LAMBDA_PROD,Excl "I_o_ID"] >> NTAC 5 $ pop_assum $ irule_at Any >>
        rpt (irule_at Any SIGMA_ALGEBRA_PROD_SIGMA_WEAK) >> simp[sigma_algebra_hist_sig_alg_n]) >>
    NTAC 3 $ pop_assum $ C (resolve_then Any assume_tac) $ cj 2 IN_MEASURABLE_BOREL_FROM_PROD_SIGMA_ALT >>
    rfs[LAMBDA_PROD] >> pop_assum irule >>
    rpt (irule_at Any SIGMA_ALGEBRA_PROD_SIGMA_WEAK) >> simp[sigma_algebra_hist_sig_alg_n]
    (* (* the map_every from below can not go in the above *)
    map_every (fn (pos,tm,qex,ths) => irule_at pos tm >> qexistsl_tac qex >> simp ths) [
        (Any,INST_TYPE [``:α`` |-> ``:ρ # σ``,``:β`` |-> ``:(α,ρ,ω) hist # σ``] IN_MEASURABLE_COMP,
            [`hist_sig_alg_n (SUC n) m_o m_a m_r × sig_alg m_s`,`λ(r,s). (hcons h w a r,s)`,`f`],[FORALL_PROD]),
        (Any,MEASURABLE_PROD_SIGMA',[],[o_DEF,UNCURRY,SF ETA_ss,IN_MEASURABLE_SND]),
        (Any,SIGMA_ALGEBRA_PROD_SIGMA_WEAK,[],[]),
        (Any,INST_TYPE [``:β`` |-> ``:ρ``] IN_MEASURABLE_COMP,
            [`sig_alg m_r`,`FST`,`hcons h w a`],[IN_MEASURABLE_FST])] >>
    *)
    (* Could be better done with general purpose measurable function slicing *)
QED

Theorem hist_lst_tonelli_SUC_step:
    ∀n (m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space) f.
        sigma_finite_measure_space m_s ∧ sigma_finite_measure_space m_o ∧
        sigma_finite_measure_space m_a ∧ sigma_finite_measure_space m_r ∧
        (∀h s. h ∈ hist_m_space_n (SUC n) m_o m_a m_r ∧ s ∈ m_space m_s ⇒ 0 ≤ f (h,s)) ∧
        f ∈ Borel_measurable (hist_sig_alg_n (SUC n) m_o m_a m_r × sig_alg m_s) ⇒
        ∫⁺ (hist_measure_space_n (SUC n) m_o m_a m_r × m_s) f =
        ∫⁺ (hist_measure_space_n n m_o m_a m_r) (λh.
        ∫⁺ (m_o × m_a × m_s × m_r) (λ(w,a,s,r). f (hcons h w a r,s)))
Proof
    rw[hist_lst_tonelli_SUC] >> irule EQ_SYM >>
    `∀h w a s r. h ∈ hist_m_space_n n m_o m_a m_r ∧ w ∈ m_space m_o ∧
      a ∈ m_space m_a ∧ s ∈ m_space m_s ∧ r ∈ m_space m_r ⇒ 0 ≤ f (hcons h w a r,s)` by (rw[] >>
        first_x_assum irule >> simp[in_hist_m_space_n]) >>
    pop_assum (fn th => qpat_x_assum `∀x. _` kall_tac >> assume_tac th) >>
    `(λ(h,w,a,s,r). f (hcons h w a r,s)) ∈ Borel_measurable
      (hist_sig_alg_n n m_o m_a m_r × sig_alg m_o × sig_alg m_a × sig_alg m_s × sig_alg m_r)` by (
        `sigma_algebra (hist_sig_alg_n n m_o m_a m_r × sig_alg m_o × sig_alg m_a ×
          sig_alg m_s × sig_alg m_r)` by (
            rpt (irule_at Any SIGMA_ALGEBRA_PROD_SIGMA_WEAK) >> simp[sigma_algebra_hist_sig_alg_n]) >>
        first_x_assum $ C (resolve_then (Pos $ el 3) irule) IN_MEASURABLE_BOREL_COMP >>
        irule_at Any SIGMA_ALGEBRA_PROD_SIGMA_WEAK >> simp[sigma_algebra_hist_sig_alg_n] >>
        qexists_tac `λ(h,w,a,s,r). (hcons h w a r,s)` >> simp[FORALL_PROD,in_mspace_prod_measure_space] >>
        rpt (irule_at Any SIGMA_ALGEBRA_PROD_SIGMA_WEAK) >> simp[sigma_algebra_hist_sig_alg_n] >>
        irule MEASURABLE_PROD_SIGMA' >> simp[o_DEF,LAMBDA_PROD] >>
        resolve_then (Pos $ el 2) (resolve_then Any
            (irule_at Any o SIMP_RULE (srw_ss ()) [sigma_algebra_hist_sig_alg_n])
            in_measure_preserving_hcons) measure_preserving_measurable IN_MEASURABLE_COMP >>
        qexists_tac `λ(h,w,a,s,r). (h,w,a,r)` >> simp[FORALL_PROD,sig_alg_prod_measure_space] >>
        rpt $ irule_at Any MEASURABLE_PROD_SIGMA' >> simp[o_DEF,LAMBDA_PROD] >>
        dxrule_then assume_tac MEASURABLE_I >>
        NTAC 4 $ pop_assum (fn th => map_every
            (C (resolve_then (Pos $ el 2) (resolve_then Any assume_tac th)) MEASURABLE_COMP)
            [IN_MEASURABLE_FST,IN_MEASURABLE_SND]) >>
        rfs[o_DEF,LAMBDA_PROD,Excl "I_o_ID"] >> NTAC 5 $ pop_assum $ irule_at Any >>
        rpt (irule_at Any SIGMA_ALGEBRA_PROD_SIGMA_WEAK >> csimp[]) >> simp[sigma_algebra_hist_sig_alg_n]) >>
    pop_assum (fn th => qpat_x_assum `_ ∈ _` kall_tac >> assume_tac th) >>
    qspecl_then [`hist_measure_space_n n m_o m_a m_r`,`m_o × m_a × m_s × m_r`] assume_tac $ cj 2 TONELLI_ALT >>
    rfs[sigma_finite_measure_space_hist_measure_space_n,sigma_finite_measure_space_prod_measure,
        in_mspace_prod_measure_space] >>
    fs[GSYM sig_alg_prod_measure_space] >> first_x_assum $ dxrule_then assume_tac >>
    rfs[LAMBDA_PROD,FORALL_PROD,Once sig_alg_prod_measure_space] >>
    NTAC 3 (irule_at Any pos_fn_integral_cong >>
        csimp[GSYM FORALL_IMP_CONJ_THM,measure_space_hist_measure_space_n] >>
        gen_tac >> DISCH_TAC >> first_x_assum $ drule_then assume_tac >>
        pop_assum (fn th => map_every (fn n => resolve_then Any assume_tac th $ cj n TONELLI_ALT) [2,6]) >>
        rfs[sigma_finite_measure_space_prod_measure,in_mspace_prod_measure_space,
            LAMBDA_PROD,FORALL_PROD,Once sig_alg_prod_measure_space] >>
        pop_assum kall_tac >> irule_at Any pos_fn_integral_pos) >>
    simp[] >> gen_tac >> DISCH_TAC >> first_x_assum $ drule_then assume_tac >>
    irule_at Any pos_fn_integral_pos >> simp[]
QED

Definition hist_obs_def:
    h_obs (hcons (h: (α,ρ,ω) hist) w a r) = w
End

Definition hist_action_def:
    h_act (hcons (h: (α,ρ,ω) hist) w a r) = a
End

Definition hist_reward_def:
    h_rew (hcons (h: (α,ρ,ω) hist) w a r) = r
End

Definition hist_hist_def:
    h_hist (hcons (h: (α,ρ,ω) hist) w a r) = h
End

Theorem hist_m_space_n_num_hsteps:
    ∀n m_o m_a m_r (h: (α,ρ,ω) hist). h ∈ hist_m_space_n n m_o m_a m_r ⇒ num_hsteps h = n
Proof
    Induct_on `n` >> rw[] >> Cases_on `h` >> fs[in_hist_m_space_n,num_hsteps_def,SF SFY_ss]
QED

Theorem num_hsteps_measurable:
    ∀m n (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space).
        measure_space m_o ∧ measure_space m_a ∧ measure_space m_r ⇒
        {h | num_hsteps h = m} ∩ hist_m_space_n n m_o m_a m_r ∈ hist_measurable_sets_n n m_o m_a m_r
Proof
    rw[] >> qspecl_then [`n`,`m_o`,`m_a`,`m_r`] assume_tac sigma_algebra_hist_sig_alg_n >>
    rfs[] >> Cases_on `m = n` >> rw[]
    >- (`{h | num_hsteps h = m} ∩ hist_m_space_n m m_o m_a m_r =
          hist_m_space_n m m_o m_a m_r` suffices_by (DISCH_THEN SUBST1_TAC >>
            dxrule_then mp_tac SIGMA_ALGEBRA_SPACE >> simp[]) >>
        irule SUBSET_INTER2 >> simp[SUBSET_DEF,hist_m_space_n_num_hsteps,SF SFY_ss])
    >- (`{h | num_hsteps h = m} ∩ hist_m_space_n n m_o m_a m_r = ∅` suffices_by (
            DISCH_THEN SUBST1_TAC >> dxrule_then mp_tac SIGMA_ALGEBRA_EMPTY >> simp[]) >>
        simp[GSYM DISJOINT_DEF,Once DISJOINT_SYM,DISJOINT_ALT] >>
        rw[] >> dxrule_then SUBST1_TAC hist_m_space_n_num_hsteps >> simp[])
QED

Theorem hist_obs_measurable:
    ∀n (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space).
        measure_space m_o ∧ measure_space m_a ∧ measure_space m_r ⇒
        h_obs ∈ measurable (hist_sig_alg_n (SUC n) m_o m_a m_r) (sig_alg m_o)
Proof
    rw[] >> simp[measurable_def,sigma_algebra_hist_sig_alg_n] >> CONJ_TAC
    >- (simp[FUNSET] >> qx_gen_tac `h` >> Cases_on `h` >> simp[in_hist_m_space_n,hist_obs_def]) >>
    qx_gen_tac `ws` >> strip_tac >> qmatch_abbrev_tac `hs ∈ _` >>
    qabbrev_tac `hr = hcons (hist_n_gen n (m_space m_o) (m_space m_a) (m_space m_r))
        ws (m_space m_a) (m_space m_r)` >>
    `hs = hist_cross hr` by (UNABBREV_ALL_TAC >> simp[EXTENSION] >> qx_gen_tac `h` >> Cases_on `h` >>
        simp[in_hist_m_space_n,hist_obs_def,in_hist_cross,GSYM hist_m_space_n_def] >>
        `∀w. w ∈ ws ⇒ w ∈ m_space m_o` suffices_by (rw[] >> eq_tac >> rw[]) >>
        simp[GSYM SUBSET_DEF,MEASURABLE_SETS_SUBSET_SPACE]) >>
    pop_assum SUBST1_TAC >> qunabbrev_tac `hs` >>
    irule $ SIMP_RULE (srw_ss ()) [SUBSET_DEF] hist_rect_set_n_measurable >>
    simp[hist_rect_sets_n_def,hist_n_gen_def] >> qexists_tac `hr` >>
    simp[Abbr `hr`,in_hist_cross,MEASURE_SPACE_SPACE,GSYM hist_m_space_n_def] >>
    Induct_on `n` >> simp[hist_n_gen_def,in_hist_cross,MEASURE_SPACE_SPACE]
QED

Theorem hist_action_measurable:
    ∀n (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space).
        measure_space m_o ∧ measure_space m_a ∧ measure_space m_r ⇒
        h_act ∈ measurable (hist_sig_alg_n (SUC n) m_o m_a m_r) (sig_alg m_a)
Proof
    rw[] >> simp[measurable_def,sigma_algebra_hist_sig_alg_n] >> CONJ_TAC
    >- (simp[FUNSET] >> qx_gen_tac `h` >> Cases_on `h` >> simp[in_hist_m_space_n,hist_action_def]) >>
    qx_gen_tac `as` >> strip_tac >> qmatch_abbrev_tac `hs ∈ _` >>
    qabbrev_tac `hr = hcons (hist_n_gen n (m_space m_o) (m_space m_a) (m_space m_r))
        (m_space m_o) as (m_space m_r)` >>
    `hs = hist_cross hr` by (UNABBREV_ALL_TAC >> simp[EXTENSION] >> qx_gen_tac `h` >> Cases_on `h` >>
        simp[in_hist_m_space_n,hist_action_def,in_hist_cross,GSYM hist_m_space_n_def] >>
        `∀a. a ∈ as ⇒ a ∈ m_space m_a` suffices_by (rw[] >> eq_tac >> rw[]) >>
        simp[GSYM SUBSET_DEF,MEASURABLE_SETS_SUBSET_SPACE]) >>
    pop_assum SUBST1_TAC >> qunabbrev_tac `hs` >>
    irule $ SIMP_RULE (srw_ss ()) [SUBSET_DEF] hist_rect_set_n_measurable >>
    simp[hist_rect_sets_n_def,hist_n_gen_def] >> qexists_tac `hr` >>
    simp[Abbr `hr`,in_hist_cross,MEASURE_SPACE_SPACE,GSYM hist_m_space_n_def] >>
    Induct_on `n` >> simp[hist_n_gen_def,in_hist_cross,MEASURE_SPACE_SPACE]
QED

Theorem hist_reward_measurable:
    ∀n (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space).
        measure_space m_o ∧ measure_space m_a ∧ measure_space m_r ⇒
        h_rew ∈ measurable (hist_sig_alg_n (SUC n) m_o m_a m_r) (sig_alg m_r)
Proof
    rw[] >> simp[measurable_def,sigma_algebra_hist_sig_alg_n] >> CONJ_TAC
    >- (simp[FUNSET] >> qx_gen_tac `h` >> Cases_on `h` >> simp[in_hist_m_space_n,hist_reward_def]) >>
    qx_gen_tac `rs` >> strip_tac >> qmatch_abbrev_tac `hs ∈ _` >>
    qabbrev_tac `hr = hcons (hist_n_gen n (m_space m_o) (m_space m_a) (m_space m_r))
        (m_space m_o) (m_space m_a) rs` >>
    `hs = hist_cross hr` by (UNABBREV_ALL_TAC >> simp[EXTENSION] >> qx_gen_tac `h` >> Cases_on `h` >>
        simp[in_hist_m_space_n,hist_reward_def,in_hist_cross,GSYM hist_m_space_n_def] >>
        `∀r. r ∈ rs ⇒ r ∈ m_space m_r` suffices_by (rw[] >> eq_tac >> rw[]) >>
        simp[GSYM SUBSET_DEF,MEASURABLE_SETS_SUBSET_SPACE]) >>
    pop_assum SUBST1_TAC >> qunabbrev_tac `hs` >>
    irule $ SIMP_RULE (srw_ss ()) [SUBSET_DEF] hist_rect_set_n_measurable >>
    simp[hist_rect_sets_n_def,hist_n_gen_def] >> qexists_tac `hr` >>
    simp[Abbr `hr`,in_hist_cross,MEASURE_SPACE_SPACE,GSYM hist_m_space_n_def] >>
    Induct_on `n` >> simp[hist_n_gen_def,in_hist_cross,MEASURE_SPACE_SPACE]
QED

Theorem hist_hist_measurable:
    ∀n (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space).
        measure_space m_o ∧ measure_space m_a ∧ measure_space m_r ⇒
        h_hist ∈ measurable (hist_sig_alg_n (SUC n) m_o m_a m_r) (hist_sig_alg_n n m_o m_a m_r)
Proof
    rw[] >> simp[measurable_def,sigma_algebra_hist_sig_alg_n] >> CONJ_TAC
    >- (simp[FUNSET] >> qx_gen_tac `h` >> Cases_on `h` >> simp[in_hist_m_space_n,hist_hist_def]) >>
    qx_gen_tac `hs` >> strip_tac >> qmatch_abbrev_tac `hsp ∈ _` >>
    qabbrev_tac `hr = hstep_cross hs (m_space m_o) (m_space m_a) (m_space m_r)` >>
    `hsp = hr` by (UNABBREV_ALL_TAC >> simp[EXTENSION] >> qx_gen_tac `h` >> Cases_on `h` >>
        simp[in_hist_m_space_n,hist_hist_def,in_hstep_cross,GSYM hist_m_space_n_def] >>
        `∀h. h ∈ hs ⇒ h ∈ hist_m_space_n n m_o m_a m_r` suffices_by (rw[] >> eq_tac >> rw[]) >>
        `sigma_algebra (hist_sig_alg_n n m_o m_a m_r)` by simp[sigma_algebra_hist_sig_alg_n] >>
        dxrule_then mp_tac SIGMA_ALGEBRA_SUBSET_SPACE >> simp[GSYM SUBSET_DEF]) >>
    pop_assum SUBST1_TAC >> qunabbrev_tac `hsp` >>
    irule $ SIMP_RULE (srw_ss ()) [SUBSET_DEF] hstep_rect_set_n_measurable >>
    simp[hstep_rect_sets_n_def] >> qunabbrev_tac `hr` >>
    qexistsl_tac [`hs`,`m_space m_o`,`m_space m_a`,`m_space m_r`] >>
    simp[MEASURE_SPACE_SPACE]
QED

Definition traj_hist_def:
    t_hist (init s) = hnil ∧
    t_hist (tcons (h: (α,ρ,σ,ω) traj) w a s r) = hcons (t_hist h) w a r
End

Theorem traj_m_space_n_hist_m_space_n:
    ∀n (m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space) h.
        h ∈ traj_m_space_n n m_s m_o m_a m_r ⇒ t_hist h ∈ hist_m_space_n n m_o m_a m_r
Proof
    Induct_on `n` >> Cases_on `h` >> fs[traj_hist_def,in_traj_m_space_n,in_hist_m_space_n] >>
    rw[] >> first_x_assum irule >> qexists_tac `m_s` >> simp[]
QED

Theorem in_measurable_traj_hist:
    ∀n (m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space).
        measure_space m_s ∧ measure_space m_o ∧ measure_space m_a ∧ measure_space m_r ⇒
        t_hist ∈ measurable (traj_sig_alg_n n m_s m_o m_a m_r) (hist_sig_alg_n n m_o m_a m_r)
Proof
    rw[] >> Cases_on `m_space m_s = ∅`
    >- (simp[IN_MEASURABLE,sigma_algebra_traj_sig_alg_n,sigma_algebra_hist_sig_alg_n,FUNSET] >>
        `traj_m_space_n n m_s m_o m_a m_r = ∅` suffices_by (rw[] >>
            simp[GSYM subsets_traj_sig_alg,Excl "subsets_traj_sig_alg"] >> irule SIGMA_ALGEBRA_EMPTY >>
            simp[sigma_algebra_traj_sig_alg_n]) >>
        simp[EXTENSION] >> qx_gen_tac `h` >> Cases_on `n` >> Cases_on `h` >> simp[in_traj_m_space_n]) >>
    fs[GSYM MEMBER_NOT_EMPTY] >> rename [`s ∈ m_space _`] >> Induct_on `n` >> rw[IN_MEASURABLE_ALT]
    >| [qexistsl_tac [`step_rect_sets_n 0 m_s m_o m_a m_r`,`hstep_rect_sets_n 0 m_o m_a m_r`],
        qexistsl_tac [`step_rect_sets_n (SUC n) m_s m_o m_a m_r`,`hstep_rect_sets_n (SUC n) m_o m_a m_r`]] >>
    simp[traj_sig_alg_n_def,traj_measurable_sets_n_alt,hist_sig_alg_n_def,hist_measurable_sets_n_alt,SIGMA_REDUCE,
        MEASURE_SPACE_SUBSET_CLASS,subset_class_step_rect_sets_n,subset_class_hstep_rect_sets_n] >>
    CONJ_TAC
    >- (simp[FUNSET] >> qx_gen_tac `h` >> Cases_on `h` >> simp[in_traj_m_space_n,traj_hist_def,in_hist_m_space_n])
    >- (simp[in_step_rect_sets_n,in_hstep_rect_sets_n] >> qexists_tac `m_space m_s` >>
        simp[MEASURE_SPACE_SPACE,EXTENSION] >> qx_gen_tac `h` >> Cases_on `h` >>
        simp[in_traj_cross,in_hist_cross,traj_hist_def,in_traj_m_space_n])
    >- (simp[FUNSET] >> qx_gen_tac `h` >> Cases_on `h` >>
        simp[in_traj_m_space_n,traj_hist_def,in_hist_m_space_n] >> rw[] >> fs[IN_MEASURABLE,FUNSET])
    >- (qx_gen_tac `hr` >> simp[in_step_rect_sets_n,in_hstep_rect_sets_n] >> rw[] >>
        fs[IN_MEASURABLE] >> first_x_assum $ drule_then assume_tac >>
        qexistsl_tac [`PREIMAGE t_hist hs ∩ traj_m_space_n n m_s m_o m_a m_r`,`ws`,`as`,`m_space m_s`,`rs`] >>
        simp[MEASURE_SPACE_SPACE,EXTENSION] >> qx_gen_tac `h` >> Cases_on `h` >>
        simp[in_step_cross,in_hstep_cross,traj_hist_def,in_traj_m_space_n] >>
        eq_tac >> rw[] >> simp[MEASURE_SPACE_IN_MSPACE,SF SFY_ss])
QED

Theorem traj_num_steps_alt:
    num_steps: ((α,ρ,σ,ω) traj -> num) = num_hsteps ∘ t_hist
Proof
    rw[FUN_EQ_THM] >> rename [`_ h = _`] >> Induct_on `h` >>
    simp[num_steps_def,num_hsteps_def,traj_hist_def]
QED

Definition hist_lst_pdf_def:
    hist_lst_pdf m_s d0 P Z R bet hnil t = (d0 t):extreal ∧
    hist_lst_pdf m_s d0 P Z R bet (hcons (h: (α,ρ,ω) hist) w a r) t = bet w a *
        ∫⁺ m_s (λs. hist_lst_pdf m_s d0 P Z R bet h s * Z s w * P s a t * R s a t r)
End

Definition hist_pdf_def:
    hist_pdf m_s d0 P Z R bet (h: (α,ρ,ω) hist) = ∫⁺ m_s (hist_lst_pdf m_s d0 P Z R bet h)
End

Theorem hist_lst_pdf_pos:
    ∀n m_s m_o m_a m_r d0 P Z R bet (h: (α,ρ,ω) hist) (s: σ).
        measure_space m_s ∧ valid_dist_gen_funs m_s m_o m_a m_r d0 P Z R bet ∧
        h ∈ hist_m_space_n n m_o m_a m_r ∧ s ∈ m_space m_s ⇒ 0 ≤ hist_lst_pdf m_s d0 P Z R bet h s
Proof
    NTAC 10 gen_tac >> simp[GSYM AND_IMP_INTRO,RIGHT_FORALL_IMP_THM] >> NTAC 2 DISCH_TAC >>
    Induct_on `n` >> qx_gen_tac `h` >> Cases_on `h` >> simp[in_hist_m_space_n] >>
    fs[valid_dist_gen_funs_def,hist_lst_pdf_def] >> rw[] >> irule le_mul >> simp[] >>
    irule pos_fn_integral_pos >> rw[] >> NTAC 3 $ irule_at Any le_mul >> simp[]
QED

Theorem hist_pdf_n_pos:
    ∀n m_s m_o m_a m_r d0 P Z R bet h s. measure_space m_s ∧
        valid_dist_gen_funs m_s m_o m_a m_r d0 P Z R bet ∧
        h ∈ hist_m_space_n n m_o m_a m_r ⇒ 0 ≤ hist_pdf m_s d0 P Z R bet h
Proof
    rw[hist_pdf_def] >> irule pos_fn_integral_pos >> simp[hist_lst_pdf_pos,SF SFY_ss]
QED

Theorem in_measurable_borel_hsans_hist_lst_pdf:
    ∀n (m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space) d0 P Z R bet.
        sigma_finite_measure_space m_s ∧ sigma_finite_measure_space m_o ∧
        sigma_finite_measure_space m_a ∧ sigma_finite_measure_space m_r ∧
        valid_dist_gen_funs m_s m_o m_a m_r d0 P Z R bet ⇒
        UNCURRY (hist_lst_pdf m_s d0 P Z R bet) ∈ Borel_measurable (hist_sig_alg_n n m_o m_a m_r × sig_alg m_s)
Proof
    rw[] >>
    drule_at_then (Pos (el 2)) assume_tac hist_lst_pdf_pos >> simp[ELIM_UNCURRY_PAIRARG] >>
    rfs[valid_dist_gen_funs_def,sig_alg_prod_measure_space] >> Induct_on `n`
    >- (map_every (fn (pos,tm,qex,ths) => irule_at pos tm >> qexistsl_tac qex >> simp ths) [
            (Any,IN_MEASURABLE_BOREL_CONG,[`d0 ∘ SND`],[]),
            (Any,INST_TYPE [``:α`` |-> ``:(α,ρ,ω) hist # σ``,``:β`` |-> ``:σ``] IN_MEASURABLE_BOREL_COMP,
                [`SND`,`d0`,`sig_alg m_s`],[]),
            (Any,SIGMA_ALGEBRA_PROD_SIGMA_WEAK,[],[])] >>
        simp[sigma_algebra_hist_sig_alg_n,IN_MEASURABLE_SND,FORALL_PROD,IN_SPACE_PROD_SIGMA] >>
        qx_gen_tac `h` >> Cases_on `h` >> rw[in_hist_m_space_n,hist_lst_pdf_def]) >>
    map_every qabbrev_tac [
        `pdf_rec = (λ(sht: σ # (α,ρ,ω) hist # σ). hist_lst_pdf m_s d0 P Z R bet (h_hist (FST (SND sht))) (FST sht))`,
        `Z_rec = (λ(sht: σ # (α,ρ,ω) hist # σ). Z (FST sht) (h_obs (FST (SND sht))))`,
        `bet_rec = (λ(ht: (α,ρ,ω) hist # σ). bet (h_obs (FST ht)) (h_act (FST ht)))`,
        `P_rec = (λ(sht: σ # (α,ρ,ω) hist # σ). P (FST sht) (h_act (FST (SND sht))) (SND (SND sht)))`,
        `R_rec = (λ(sht: σ # (α,ρ,ω) hist # σ).
            R (FST sht) (h_act (FST (SND sht))) (SND (SND sht)) (h_rew (FST (SND sht))))`,
        `int_rec = (λ(sht: σ # (α,ρ,ω) hist # σ). pdf_rec sht * Z_rec sht * P_rec sht * R_rec sht)`] >>
    map_every (fn (pos,tm,qex,ths) => irule_at pos tm >> qexistsl_tac qex >> simp ths) [
        (Any,IN_MEASURABLE_BOREL_CONG,[`λht. bet_rec ht * ∫⁺ m_s (λs. int_rec (s,ht))`],[]),
        (Any,IN_MEASURABLE_BOREL_MUL',[`λht. ∫⁺ m_s (λs. int_rec (s,ht))`,`bet_rec`],[]),
        (Any,SIMP_RULE (srw_ss ()) [sig_alg_prod_measure_space] $ ISPECL [``m_s: σ m_space``,
            ``((hist_measure_space_n (SUC n) m_o m_a m_r) × m_s): ((α,ρ,ω) hist # σ) m_space``]
            (cj 4 TONELLI_ALT),[],[Abbr `bet_rec`]),
        (Any,sigma_finite_measure_space_prod_measure,[],[sigma_finite_measure_space_hist_measure_space_n]),
        (Pos (el 4),INST_TYPE [``:α`` |-> ``:(α,ρ,ω) hist # σ``,``:β`` |-> ``:ω # α``] IN_MEASURABLE_COMP,
            [`(λ(w,a). bet w a)`,`λht. (h_obs (FST ht),h_act (FST ht))`,`sig_alg m_o × sig_alg m_a`],[]),
        (Any,IN_MEASURABLE_PROD_SIGMA,[`h_act ∘ FST`,`h_obs ∘ FST`],[Abbr `int_rec`]),
        (Pos (el 3),IN_MEASURABLE_BOREL_MUL',[`R_rec`,`λsht. pdf_rec sht * Z_rec sht * P_rec sht`],[Abbr `R_rec`]),
        (Pos (el 3),INST_TYPE [``:α`` |-> ``:σ # (α,ρ,ω) hist # σ``,``:β`` |-> ``:σ # α # σ # ρ``] IN_MEASURABLE_COMP,
            [`(λ(s,a,t,r). R s a t r)`,`λsht. (FST sht,h_act (FST (SND sht)),SND (SND sht),h_rew (FST (SND sht)))`,
            `sig_alg m_s × sig_alg m_a × sig_alg m_s × sig_alg m_r`],[]),
        (Pos hd,IN_MEASURABLE_PROD_SIGMA,
            [`λsht. (h_act (FST (SND sht)),SND (SND sht),h_rew (FST (SND sht)))`,`FST`],[]),
        (Pos (el 2),IN_MEASURABLE_PROD_SIGMA,[`λsht. (SND (SND sht),h_rew (FST (SND sht)))`,`h_act ∘ FST ∘ SND`],[]),
        (Pos (el 2),IN_MEASURABLE_PROD_SIGMA,[`h_rew ∘ FST ∘ SND`,`SND ∘ SND`],[]),
        (Pos (el 6),IN_MEASURABLE_BOREL_MUL',[`P_rec`,`λsht. pdf_rec sht * Z_rec sht`],[Abbr `P_rec`]),
        (Pos (el 2),INST_TYPE [``:α`` |-> ``:σ # (α,ρ,ω) hist # σ``,``:β`` |-> ``:σ # α # σ``] IN_MEASURABLE_COMP,
            [`(λ(s,a,t). P s a t)`,`λsht. (FST sht,h_act (FST (SND sht)),SND (SND sht))`,
            `sig_alg m_s × sig_alg m_a × sig_alg m_s`],[]),
        (Pos hd,IN_MEASURABLE_PROD_SIGMA,[`λsht. (h_act (FST (SND sht)),SND (SND sht))`,`FST`],[SF CONJ_ss]),
        (Pos hd,IN_MEASURABLE_PROD_SIGMA,[`SND ∘ SND`,`h_act ∘ FST ∘ SND`],[SF CONJ_ss]),
        (Pos hd,IN_MEASURABLE_BOREL_MUL',[`Z_rec`,`pdf_rec`],[Abbr `Z_rec`]),
        (Pos (el 2),INST_TYPE [``:α`` |-> ``:σ # (α,ρ,ω) hist # σ``,``:β`` |-> ``:σ # ω``] IN_MEASURABLE_COMP,
            [`(λ(s,w). Z s w)`,`λsht. (FST sht,h_obs (FST (SND sht)))`,`sig_alg m_s × sig_alg m_o`],[]),
        (Pos hd,IN_MEASURABLE_PROD_SIGMA,[`h_obs ∘ FST ∘ SND`,`FST`],[SF CONJ_ss,Abbr `pdf_rec`]),
        (Pos (el 2),INST_TYPE [``:α`` |-> ``:σ # (α,ρ,ω) hist # σ``,``:β`` |-> ``:(α,ρ,ω) hist # σ``] IN_MEASURABLE_COMP,
            [`(λ(h,t). hist_lst_pdf m_s d0 P Z R bet h t)`,`λsht. (h_hist (FST (SND sht)),FST sht)`,
            `hist_sig_alg_n n m_o m_a m_r × sig_alg m_s`],[]),
        (Pos hd,IN_MEASURABLE_PROD_SIGMA,[`FST`,`h_hist ∘ FST ∘ SND`],[SF CONJ_ss]),
        (Pos (el 5),INST_TYPE [``:α`` |-> ``:σ # (α,ρ,ω) hist # σ``,``:β`` |-> ``:(α,ρ,ω) hist``] MEASURABLE_COMP,
            [`hist_sig_alg_n (SUC n) m_o m_a m_r`],[]),
        (Pos (el 6),INST_TYPE [``:α`` |-> ``:σ # (α,ρ,ω) hist # σ``,``:β`` |-> ``:(α,ρ,ω) hist``] MEASURABLE_COMP,
            [`hist_sig_alg_n (SUC n) m_o m_a m_r`],[SF CONJ_ss]),
        (Pos (el 5),INST_TYPE [``:α`` |-> ``:σ # (α,ρ,ω) hist # σ``,``:β`` |-> ``:(α,ρ,ω) hist``] MEASURABLE_COMP,
            [`hist_sig_alg_n (SUC n) m_o m_a m_r`],[SF CONJ_ss]),
        (Pos (el 5),INST_TYPE [``:α`` |-> ``:σ # (α,ρ,ω) hist # σ``,``:β`` |-> ``:(α,ρ,ω) hist``] MEASURABLE_COMP,
            [`hist_sig_alg_n (SUC n) m_o m_a m_r`],[SF CONJ_ss]),
        (Any,INST_TYPE [``:α`` |-> ``:σ # (α,ρ,ω) hist # σ``,``:β`` |-> ``:(α,ρ,ω) hist # σ``] MEASURABLE_COMP,
            [`hist_sig_alg_n (SUC n) m_o m_a m_r × sig_alg m_s`],[]),
        (Any,INST_TYPE [``:α`` |-> ``:σ # (α,ρ,ω) hist # σ``,``:β`` |-> ``:(α,ρ,ω) hist # σ``] MEASURABLE_COMP,
            [`hist_sig_alg_n (SUC n) m_o m_a m_r × sig_alg m_s`],[SF CONJ_ss]),
        (Any,INST_TYPE [``:α`` |-> ``:(α,ρ,ω) hist # σ``,``:β`` |-> ``:(α,ρ,ω) hist``] MEASURABLE_COMP,
            [`hist_sig_alg_n (SUC n) m_o m_a m_r`],[SF CONJ_ss]),
        (Any,INST_TYPE [``:α`` |-> ``:(α,ρ,ω) hist # σ``,``:β`` |-> ``:(α,ρ,ω) hist``] MEASURABLE_COMP,
            [`hist_sig_alg_n (SUC n) m_o m_a m_r`],[SF CONJ_ss]),
        (Any,SIGMA_ALGEBRA_PROD_SIGMA_WEAK,[],[]),
        (Any,IN_MEASURABLE_FST,[],[]),(Any,IN_MEASURABLE_FST,[],[]),
        (Any,IN_MEASURABLE_SND,[],[]),(Any,IN_MEASURABLE_SND,[],[]),
        (Any,SIGMA_ALGEBRA_PROD_SIGMA_WEAK,[],[sigma_algebra_hist_sig_alg_n])] >>
    simp[hist_obs_measurable,hist_action_measurable,hist_reward_measurable,hist_hist_measurable] >> CONJ_TAC >>
    simp[FORALL_PROD,IN_SPACE_PROD_SIGMA,in_mspace_prod_measure_space] >| [qx_gen_tac `s`,all_tac] >>
    qx_genl_tac [`h`,`t`] >> Cases_on `h` >>
    simp[in_hist_m_space_n,hist_obs_def,hist_action_def,hist_reward_def,hist_hist_def,hist_lst_pdf_def] >>
    rw[] >> NTAC 3 $ irule_at Any le_mul >> simp[SF SFY_ss]
QED

Theorem hist_lst_pdf_tonelli_0:
    ∀(m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space) d0 P Z R bet f.
        sigma_finite_measure_space m_s ∧ sigma_finite_measure_space m_o ∧
        sigma_finite_measure_space m_a ∧ sigma_finite_measure_space m_r ∧
        valid_dist_gen_funs m_s m_o m_a m_r d0 P Z R bet ∧
        (∀h s. h ∈ hist_m_space_n 0 m_o m_a m_r ∧ s ∈ m_space m_s ⇒ 0 ≤ f (h,s)) ∧
        f ∈ Borel_measurable (hist_sig_alg_n 0 m_o m_a m_r × sig_alg m_s) ⇒
        ∫⁺ (density (hist_measure_space_n 0 m_o m_a m_r × m_s) (UNCURRY (hist_lst_pdf m_s d0 P Z R bet))) f =
        ∫⁺ (density m_s d0) (λs. f (hnil,s))
Proof
    rw[] >> qmatch_abbrev_tac `_ (_ m_hs hspdf) _ = _ _ g` >>
    `∫⁺ (density m_hs hspdf) f = ∫⁺ m_hs (λh. hspdf h * f h) ∧ ∫⁺ (density m_s d0) g = ∫⁺ m_s (λs. d0 s * g s) ∧
        ∫⁺ m_hs (λh. hspdf h * f h) = ∫⁺ m_s (λs. d0 s * g s)` suffices_by simp[] >>
    NTAC 2 $ irule_at Any pos_fn_integral_density_clean >> UNABBREV_ALL_TAC >> simp[] >>
    qspecl_then [`m_s`,`m_o`,`m_a`,`m_r`,`λhs. UNCURRY (hist_lst_pdf m_s d0 P Z R bet) hs * f hs`]
        (irule_at Any o SIMP_RULE (srw_ss ()) [hist_lst_pdf_def]) hist_lst_tonelli_0 >>
    `hnil ∈ hist_m_space_n 0 m_o m_a m_r` by simp[in_hist_m_space_n] >>
    simp[sig_alg_prod_measure_space,FORALL_PROD,m_space_prod_measure_space,iffLR valid_dist_gen_funs_def,
        hist_lst_pdf_pos,le_mul,SF SFY_ss] >>
    map_every (fn (pos,tm,qex,ths) => irule_at pos tm >> qexistsl_tac qex >> simp ths) [
        (Any,measure_space_prod_measure,[],[sigma_finite_measure_space_hist_measure_space_0]),
        (Pos hd,IN_MEASURABLE_BOREL_MUL',[`f`,`UNCURRY (hist_lst_pdf m_s d0 P Z R bet)`],[SF CONJ_ss]),
        (Any,in_measurable_borel_hsans_hist_lst_pdf,[],[]),
        (Any,cj 2 IN_MEASURABLE_BOREL_FROM_PROD_SIGMA_ALT,[`hist_sig_alg_n 0 m_o m_a m_r`],[]),
        (Any,SIGMA_ALGEBRA_PROD_SIGMA_WEAK,[],[sigma_algebra_hist_sig_alg_0])]
QED

Theorem in_measurable_borel_hsan_hist_pdf:
    ∀n (m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space) d0 P Z R bet.
        sigma_finite_measure_space m_s ∧ sigma_finite_measure_space m_o ∧
        sigma_finite_measure_space m_a ∧ sigma_finite_measure_space m_r ∧
        valid_dist_gen_funs m_s m_o m_a m_r d0 P Z R bet ⇒
        hist_pdf m_s d0 P Z R bet ∈ Borel_measurable (hist_sig_alg_n n m_o m_a m_r)
Proof
    rw[] >>
    qspecl_then [`hist_measure_space_n n m_o m_a m_r`,`m_s`,`λ(h,t). hist_lst_pdf m_s d0 P Z R bet h t`]
        mp_tac $ cj 3 TONELLI_ALT >>
    simp[SF ETA_ss,GSYM hist_pdf_def] >> DISCH_THEN irule >>
    simp[sigma_finite_measure_space_hist_measure_space_n,in_measurable_borel_hsans_hist_lst_pdf,
        FORALL_PROD,hist_lst_pdf_pos,SF SFY_ss]
QED

Definition h_importance_ratio_def:
    h_importance_ratio phi bet hnil = 1:extreal ∧
    h_importance_ratio phi bet (hcons (h: (α,ρ,ω) hist) w a r) =
        h_importance_ratio phi bet h * phi w a * (bet w a)⁻¹
End

Theorem traj_importance_ratio_alt:
    ∀phi bet. (importance_ratio phi bet): ((α,ρ,σ,ω) traj -> extreal) =
        h_importance_ratio phi bet ∘ t_hist
Proof
    rw[FUN_EQ_THM] >> rename [`_ _ _ h`] >> Induct_on `h` >>
    simp[importance_ratio_def,h_importance_ratio_def,traj_hist_def]
QED

Theorem in_measurable_borel_hsan_importance_ratio:
    ∀n (m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space) d0 P Z R bet phi.
        measure_space m_o ∧ measure_space m_a ∧ measure_space m_r ∧
        valid_dist_gen_funs m_s m_o m_a m_r d0 P Z R bet ∧
        valid_dist_gen_funs m_s m_o m_a m_r d0 P Z R phi ∧
        (∀w a. w ∈ m_space m_o ∧ a ∈ m_space m_a ∧ bet w a = 0 ⇒ phi w a = 0) ⇒
        h_importance_ratio phi bet ∈ Borel_measurable (hist_sig_alg_n n m_o m_a m_r)
Proof
    rpt gen_tac >> DISCH_TAC >> fs[valid_dist_gen_funs_def] >> gvs[] >>
    `∀n. sigma_algebra (hist_sig_alg_n n m_o m_a m_r)` by simp[sigma_algebra_hist_sig_alg_n] >>
    Induct_on `n` >> rw[]
    >- (irule IN_MEASURABLE_BOREL_CONG >> qexists_tac `λx. 1` >> simp[IN_MEASURABLE_BOREL_CONST'] >>
        qx_gen_tac `h` >> Cases_on `h` >> simp[in_hist_m_space_n,h_importance_ratio_def]) >>
    map_every (fn (pos,tm,qex,ths) => irule_at pos tm >> qexistsl_tac qex >> simp ths) [
        (Any,IN_MEASURABLE_BOREL_CONG,
            [`λh. h_importance_ratio phi bet (h_hist h) * phi (h_obs h) (h_act h) * (bet (h_obs h) (h_act h))⁻¹`],[]),
        (Any,IN_MEASURABLE_BOREL_MUL',[`λh. phi (h_obs h) (h_act h) * (bet (h_obs h) (h_act h))⁻¹`,
            `h_importance_ratio phi bet ∘ h_hist`],[mul_assoc]),
        (Pos hd,INST_TYPE [``:β`` |-> ``:α``] IN_MEASURABLE_BOREL_COMP,
            [`h_hist`,`h_importance_ratio phi bet`,`hist_sig_alg_n n m_o m_a m_r`],[]),
        (Pos (el 2),INST_TYPE [``:α`` |-> ``:(α,ρ,ω) hist``,``:β`` |-> ``:ω # α``] IN_MEASURABLE_BOREL_COMP,
            [`λh. (h_obs h,h_act h)`,`λ(w,a). phi w a * (bet w a)⁻¹`,`sig_alg (m_o × m_a)`],
            [sig_alg_prod_measure_space]),
        (Pos (el 3),IN_MEASURABLE_PROD_SIGMA,[`h_act`,`h_obs`],[]),
        (Pos (el 4),IN_MEASURABLE_BOREL_MUL_INV,[`λ(w,a). bet w a`,`λ(w,a). phi w a`],
            [Ntimes (GSYM sig_alg_prod_measure_space) 2,IN_SPACE_PROD_SIGMA,PAIR_FUN2]),
        (Any,SIGMA_ALGEBRA_PROD_SIGMA_WEAK,[],[])] >>
    simp[hist_obs_measurable,hist_action_measurable,hist_hist_measurable] >> qx_gen_tac `h` >> Cases_on `h` >>
    simp[in_hist_m_space_n,h_importance_ratio_def,hist_obs_def,hist_action_def,hist_hist_def]
QED

Definition hist_return_def:
    hist_return g hnil = 0 ∧
    hist_return g (hcons (h: (α,extreal,ω) hist) w a r) = hist_return g h + (g pow (num_hsteps h)) * r
End

Theorem traj_return_alt:
    ∀g. (traj_return g): ((α,extreal,σ,ω) traj -> extreal) = hist_return g ∘ t_hist
Proof
    rw[FUN_EQ_THM] >> rename [`_ _ h = _`] >> Induct_on `h` >>
    simp[traj_return_def,hist_return_def,traj_hist_def] >> simp[traj_num_steps_alt]
QED

Theorem in_measurable_borel_hsan_hist_return:
    ∀n (m_o: ω m_space) (m_a: α m_space) (m_r: extreal m_space) g.
        measure_space m_o ∧ measure_space m_a ∧ measure_space m_r ∧ sig_alg m_r = Borel ⇒
        hist_return g ∈ Borel_measurable (hist_sig_alg_n n m_o m_a m_r)
Proof
    rpt gen_tac >> DISCH_TAC >> fs[] >>
    `∀n. sigma_algebra (hist_sig_alg_n n m_o m_a m_r)` by simp[sigma_algebra_hist_sig_alg_n] >>
    Induct_on `n` >> rw[]
    >- (irule IN_MEASURABLE_BOREL_CONG >> qexists_tac `λx. 0` >> simp[IN_MEASURABLE_BOREL_CONST'] >>
        qx_gen_tac `h` >> Cases_on `h` >> simp[in_hist_m_space_n,hist_return_def]) >>
    map_every (fn (pos,tm,qex,ths) => irule_at pos tm >> qexistsl_tac qex >> simp ths) [
        (Any,IN_MEASURABLE_BOREL_CONG,
            [`λh. hist_return g (h_hist h) + g pow num_hsteps (h_hist h) * h_rew h`],[]),
        (Any,IN_MEASURABLE_BOREL_ADD',
            [`λh. g pow num_hsteps (h_hist h) * h_rew h`,`λh. hist_return g (h_hist h)`],[]),
        (Pos hd,INST_TYPE [``:β`` |-> ``:α``] IN_MEASURABLE_BOREL_COMP,
            [`h_hist`,`hist_return g`,`hist_sig_alg_n n m_o m_a m_r`],[]),
        (Any,IN_MEASURABLE_BOREL_MUL',[`h_rew`,`λh. g pow num_hsteps (h_hist h)`],[]),
        (Pos hd,INST_TYPE [``:β`` |-> ``:α``] IN_MEASURABLE_BOREL_COMP,
            [`h_hist`,`λh. g pow num_hsteps h`,`hist_sig_alg_n n m_o m_a m_r`],[SF CONJ_ss]),
        (Pos hd,IN_MEASURABLE_BOREL_POW_EXP,[`num_hsteps`,`λh. g`],
            [IN_MEASURABLE_BOREL_CONST',num_hsteps_measurable])] >>
    qpat_x_assum `_ = _` $ SUBST1_TAC o SYM >> simp[hist_reward_measurable,hist_hist_measurable] >>
    qx_gen_tac `h` >> Cases_on `h` >> fs[in_hist_m_space_n] >> simp[hist_return_def,hist_hist_def,hist_reward_def]
QED

Theorem hist_pos_fn_integral_hs_pos_fn_integral:
    ∀n (m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space) d0 P Z R bet f.
        sigma_finite_measure_space m_s ∧ sigma_finite_measure_space m_o ∧
        sigma_finite_measure_space m_a ∧ sigma_finite_measure_space m_r ∧
        valid_dist_gen_funs m_s m_o m_a m_r d0 P Z R bet ∧
        (∀x. x ∈ hist_m_space_n n m_o m_a m_r ⇒ 0 ≤ f x) ∧
        f ∈ Borel_measurable (hist_sig_alg_n n m_o m_a m_r) ⇒
        ∫⁺ (density (hist_measure_space_n n m_o m_a m_r) (hist_pdf m_s d0 P Z R bet)) f =
        ∫⁺ (density (hist_measure_space_n n m_o m_a m_r × m_s) (UNCURRY (hist_lst_pdf m_s d0 P Z R bet))) (f ∘ FST)
Proof
    rw[] >> qmatch_abbrev_tac `_ (_ m_h hpdf) _ = _ (_ m_hs hspdf) g` >>
    fs[GSYM m_space_hist_measure_space,GSYM sig_alg_hist_measure_space,
        Excl "m_space_hist_measure_space",Excl "sig_alg_hist_measure_space"] >>
    `∫⁺ (density m_h hpdf) f = ∫⁺ m_h (λx. hpdf x * f x) ∧ ∫⁺ (density m_hs hspdf) g = ∫⁺ m_hs (λx. hspdf x * g x) ∧
        ∫⁺ m_h (λx. hpdf x * f x) = ∫⁺ m_hs (λx. hspdf x * g x)` suffices_by simp[] >>
    NTAC 2 $ irule_at Any pos_fn_integral_density_clean >> simp[Abbr `m_hs`,sig_alg_prod_measure_space] >>
    irule_at Any EQ_TRANS >> qexists_tac `∫⁺ m_h (λx. ∫⁺ m_s (λy. (λx. hspdf x * g x) (x,y)))` >>
    map_every (fn (pos,tm,qex,ths) => irule_at pos tm >> qexistsl_tac qex >> simp ths) [
        (Any,GSYM $ cj 6 TONELLI_ALT,[],[]),
        (Any,pos_fn_integral_cong,[],[SF CONJ_ss]),
        (Pos $ el 4,IN_MEASURABLE_BOREL_MUL',[`g`,`hspdf`],[]),
        (Any,measure_space_prod_measure,[],[]),
        (Any,SIGMA_ALGEBRA_PROD_SIGMA_WEAK,[],[SF CONJ_ss,Abbr `g`]),
        (Any,MEASURABLE_COMP,[`sig_alg m_h`],[]),
        (Any,IN_MEASURABLE_FST,[],[SF CONJ_ss])] >>
    simp[Abbr `m_h`,Abbr `hpdf`,Abbr `hspdf`,FORALL_PROD] >>
    simp[m_space_prod_measure_space,sigma_finite_measure_space_hist_measure_space_n,
        in_measurable_borel_hsan_hist_pdf,in_measurable_borel_hsans_hist_lst_pdf,
        hist_pdf_n_pos,hist_lst_pdf_pos,le_mul,SF SFY_ss] >>
    simp[GSYM FORALL_IMP_CONJ_THM] >> qx_gen_tac `h` >> DISCH_TAC >> irule_at Any pos_fn_integral_pos >>
    simp[hist_lst_pdf_pos,le_mul,SF SFY_ss,hist_pdf_def] >> simp[Once mul_comm] >> irule EQ_SYM >>
    simp[Once mul_comm] >> irule pos_fn_integral_cmult_clean >> simp[hist_lst_pdf_pos,SF SFY_ss] >>
    resolve_then Any (irule o SIMP_RULE (srw_ss ()) [SF ETA_ss])
        in_measurable_borel_hsans_hist_lst_pdf (cj 2 IN_MEASURABLE_BOREL_FROM_PROD_SIGMA_ALT) >>
    simp[] >> qexistsl_tac [`m_a`,`m_o`,`m_r`,`n`] >> simp[sigma_algebra_hist_sig_alg_n]
QED

Theorem traj_pos_fn_integral_hist_pos_fn_integral:
    ∀n (m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space) d0 P Z R bet f.
        sigma_finite_measure_space m_s ∧ sigma_finite_measure_space m_o ∧
        sigma_finite_measure_space m_a ∧ sigma_finite_measure_space m_r ∧
        valid_dist_gen_funs m_s m_o m_a m_r d0 P Z R bet ∧
        (∀x. x ∈ hist_m_space_n n m_o m_a m_r ⇒ 0 ≤ f x) ∧
        f ∈ Borel_measurable (hist_sig_alg_n n m_o m_a m_r) ⇒
        ∫⁺ (density (traj_measure_space_n n m_s m_o m_a m_r) (traj_pdf d0 P Z R bet)) (f ∘ t_hist) =
        ∫⁺ (density (hist_measure_space_n n m_o m_a m_r) (hist_pdf m_s d0 P Z R bet)) f
Proof
    NTAC 10 gen_tac >> simp[Ntimes (GSYM AND_IMP_INTRO) 5,RIGHT_FORALL_IMP_THM] >> NTAC 5 DISCH_TAC >>
    simp[hist_pos_fn_integral_hs_pos_fn_integral] >>
    `∀f. (∀h s. h ∈ hist_m_space_n n m_o m_a m_r ∧ s ∈ m_space m_s ⇒ 0 ≤ f (h,s)) ∧
      f ∈ Borel_measurable (hist_sig_alg_n n m_o m_a m_r × sig_alg m_s) ⇒
      ∫⁺ (traj_measure_space_n n m_s m_o m_a m_r) (λh. traj_pdf d0 P Z R bet h * f (t_hist h,t_st h)) =
      ∫⁺ (hist_measure_space_n n m_o m_a m_r × m_s)
      (λhs. (UNCURRY (hist_lst_pdf m_s d0 P Z R bet)) hs * f hs)` suffices_by (rw[] >>
        last_x_assum $ qspec_then `f ∘ FST` mp_tac >> simp[] >>
        DISCH_THEN $ resolve_then Any (mp_tac o Q.SPEC `hist_sig_alg_n n m_o m_a m_r`) MEASURABLE_COMP >>
        simp[sigma_algebra_hist_sig_alg_n,IN_MEASURABLE_FST,SF SFY_ss] >>
        `∀x1:extreal x2 x3 x4. x3 = x1 ∧ x4 = x2 ∧ x1 = x2 ⇒ x3 = x4` by simp[] >>
        first_x_assum $ DISCH_THEN o (C $ resolve_then (Pos $ el 3) irule) >>
        NTAC 2 $ resolve_then (Pos $ el 3) (irule_at Any o SIMP_RULE (srw_ss ()) [])
            MEASURABLE_COMP pos_fn_integral_density_clean >>
        qexistsl_tac [`hist_sig_alg_n n m_o m_a m_r`,`hist_sig_alg_n n m_o m_a m_r`] >>
        simp[sig_alg_prod_measure_space,m_space_prod_measure_space,FORALL_PROD,
            traj_m_space_n_hist_m_space_n,sigma_algebra_hist_sig_alg_n,IN_MEASURABLE_FST,
            in_measurable_traj_hist,in_measurable_borel_hsans_hist_lst_pdf,in_measurable_borel_tsan_traj_pdf,
            measure_space_traj_measure_space_n,sigma_finite_measure_space_hist_measure_space_n,
            measure_space_prod_measure,traj_pdf_n_pos,hist_lst_pdf_pos,SF SFY_ss]) >>
    Induct_on `n` >> rw[]
    >| let fun tacf (tf_tm,tf_th,hsf_tm,hsf_th,sa_tm) = qmatch_abbrev_tac `_ _ tf = _ _ hsf` >>
        map_every (fn (pos,tm,qex,ths) => irule_at pos tm >> qexistsl_tac qex >> simp ths) [
            (Any,EQ_TRANS,[tf_tm],[]),
            (Any,tf_th,[],[Abbr `tf`,o_DEF,traj_hist_def,traj_state_def,traj_pdf_def]),
            (Any,EQ_SYM,[],[]),
            (Any,EQ_TRANS,[hsf_tm],[]),
            (Any,hsf_th,[],[Abbr `hsf`,hist_lst_pdf_def,hist_lst_pdf_pos,traj_pdf_n_pos,
                traj_m_space_n_hist_m_space_n,traj_state_n_in_m_space,le_mul,SF SFY_ss]),
            (Any,IN_MEASURABLE_BOREL_MUL',[`f`,`UNCURRY (hist_lst_pdf m_s d0 P Z R bet)`],
                [in_measurable_borel_hsans_hist_lst_pdf]),
            (Any,IN_MEASURABLE_BOREL_MUL',[`λh. f (t_hist h,t_st h)`,`traj_pdf d0 P Z R bet`],
                [in_measurable_borel_tsan_traj_pdf,GSYM o_DEF]),
            (Any,MEASURABLE_COMP,[sa_tm],[]),
            (Any,MEASURABLE_PROD_SIGMA',[],[o_DEF,SF ETA_ss]),
            (Any,SIGMA_ALGEBRA_PROD_SIGMA_WEAK,[],[sigma_algebra_hist_sig_alg_n,sigma_algebra_traj_sig_alg_n,
                traj_state_measurable,in_measurable_traj_hist])] in [
        tacf (`∫⁺ m_s (tf ∘ init)`,traj_tonelli_0,`∫⁺ m_s (λs. hsf (hnil,s))`,hist_lst_tonelli_0,
            `hist_sig_alg_n 0 m_o m_a m_r × sig_alg m_s`),
        tacf (`∫⁺ (traj_measure_space_n n m_s m_o m_a m_r) (λh.
                ∫⁺ (m_o × m_a × m_s × m_r) (λ(w,a,s,r). tf (tcons h w a s r)))`,
            traj_tonelli_SUC_step,
            `∫⁺ (hist_measure_space_n n m_o m_a m_r) (λh.
                ∫⁺ (m_o × m_a × m_s × m_r) (λ(w,a,t,r). hsf (hcons h w a r,t)))`,
            hist_lst_tonelli_SUC_step,
            `hist_sig_alg_n (SUC n) m_o m_a m_r × sig_alg m_s`)] end >>
    `∀h w a s r. h ∈ hist_m_space_n n m_o m_a m_r ∧ w ∈ m_space m_o ∧
      a ∈ m_space m_a ∧ s ∈ m_space m_s ∧ r ∈ m_space m_r ⇒ 0 ≤ f (hcons h w a r,s)` by (rw[] >>
        first_x_assum irule >> simp[in_hist_m_space_n]) >>
    pop_assum (fn th => qpat_x_assum `∀h s. _` kall_tac >> assume_tac th) >> irule EQ_SYM >>
    first_x_assum $ qspec_then `λ(h,s). ∫⁺ (m_o × m_a × m_s × m_r) (λ(w,a,t,r).
        Z s w * bet w a * P s a t * R s a t r * f (hcons h w a r,t))` (fn th =>
        resolve_then Any (resolve_then (Pos $ el 2) (irule_at Any) th) EQ_TRANS EQ_TRANS) >>
    qexists_tac `f` >> irule_at (Pos $ el 2) EQ_SYM >>
    irule_at (Pos hd) pos_fn_integral_cong >> csimp[LAMBDA_PROD] >>
    qspecl_then [`hist_measure_space_n n m_o m_a m_r`,`m_s`,
        `λ(h,s). ∫⁺ (m_o × m_a × m_s × m_r) (λ(w,a,t,r). hist_lst_pdf m_s d0 P Z R bet h s *
          Z s w * bet w a * P s a t * R s a t r * f (hcons h w a r,t))`] assume_tac $ cj 6 TONELLI_ALT >>
    pop_assum (fn th => resolve_then Any (resolve_then (Pos $ el 2) (irule_at Any) th) EQ_TRANS EQ_TRANS) >>
    csimp[] >> irule_at (Pos $ el 5) EQ_SYM >> irule_at (Pos hd) EQ_TRANS >>
    qexists_tac `∫⁺ (hist_measure_space_n n m_o m_a m_r) (λh. ∫⁺ (m_o × m_a × m_s × m_r) (λ(w,a,t,r). ∫⁺ m_s (λs.
        hist_lst_pdf m_s d0 P Z R bet h s * Z s w * bet w a * P s a t * R s a t r * f (hcons h w a r,t))))` >>
    NTAC 3 $ irule_at Any pos_fn_integral_cong >> simp[] >>
    ConseqConv.CONSEQ_REWRITE_TAC ([pos_fn_integral_cong],[],[]) >>
    csimp[FORALL_PROD,LAMBDA_PROD,in_mspace_prod_measure_space] >>
    irule_at Any measure_space_prod_measure >>
    simp[sigma_finite_measure_space_hist_measure_space_n,measure_space_traj_measure_space_n] >>
    `measure_space (m_o × m_a × m_s × m_r)` by simp[sigma_finite_measure_space_prod_measure] >>
    qspecl_then [`m_o × m_a × m_s × m_r`,`λ(w,a,t,r). Z s w * bet w a * P s a t * R s a t r *
        f (hcons h w a r,t)`] (fn th => ConseqConv.CONSEQ_REWRITE_TAC
        ([SIMP_RULE (srw_ss ()) [LAMBDA_PROD,mul_assoc] th],[],[])) $ GSYM pos_fn_integral_cmult_clean >>
    resolve_then Any (resolve_then Any (qspecl_then [`m_o × m_a × m_s × m_r`,`m_s`,`λ(s,w,a,t,r).
        hist_lst_pdf m_s d0 P Z R bet h s * Z s w * bet w a * P s a t * R s a t r * f (hcons h w a r,t)`]
        (fn th => ConseqConv.CONSEQ_REWRITE_TAC ([SIMP_RULE (srw_ss ()) [LAMBDA_PROD] th],[],[]))) $
        cj 6 TONELLI_ALT) (GSYM $ cj 5 TONELLI_ALT) EQ_TRANS >>
    `∀h w a t r. ∫⁺ m_s (λs. hist_lst_pdf m_s d0 P Z R bet h s * Z s w * bet w a * P s a t *
      R s a t r * f (hcons h w a r,t)) = ∫⁺ m_s (λs. bet w a * f (hcons h w a r,t) *
      hist_lst_pdf m_s d0 P Z R bet h s * Z s w * P s a t * R s a t r)` by (rw[] >>
        irule IRULER >> rw[FUN_EQ_THM] >> metis_tac[mul_comm,mul_assoc]) >>
    simp[] >> pop_assum kall_tac >>
    `∀h w a t r x. bet w a * x * f (hcons h w a t,r) = bet w a * f (hcons h w a t,r) * x` by (rw[] >>
        rw[FUN_EQ_THM] >> metis_tac[mul_comm,mul_assoc]) >>
    simp[] >> pop_assum kall_tac >>
    qspecl_then [`m_s`,`λs. hist_lst_pdf m_s d0 P Z R bet h s * Z s w * P s a t * R s a t r`,
        `bet w a * f (hcons h w a r,t)`]
        (fn th => ConseqConv.CONSEQ_REWRITE_TAC ([SIMP_RULE (srw_ss ()) [LAMBDA_PROD,mul_assoc] th],[],[])) $
        GSYM pos_fn_integral_cmult_clean >>
    map_every (fn f_tm => qspecl_then [`hist_measure_space_n n m_o m_a m_r × m_s`,`m_o × m_a × m_s × m_r`,f_tm]
        (irule_at Any o SIMP_RULE (srw_ss ()) [FORALL_PROD,LAMBDA_PROD,sig_alg_prod_measure_space]) $
        cj 3 TONELLI_ALT) [`λ((h,s),w,a,t,r). hist_lst_pdf m_s d0 P Z R bet h s * Z s w * bet w a *
        P s a t * R s a t r * f (hcons h w a r,t)`,`λ((h,s),w,a,t,r).
        Z s w * bet w a * P s a t * R s a t r * f (hcons h w a r,t)`] >>
    csimp[] >> rpt $ irule_at Any sigma_finite_measure_space_prod_measure >>
    simp[sigma_finite_measure_space_hist_measure_space_n] >>
    rpt (ConseqConv.CONSEQ_REWRITE_TAC ([pos_fn_integral_pos,le_mul,hist_lst_pdf_pos,traj_pdf_n_pos],[],[]) >>
        simp[FORALL_PROD,ELIM_UNCURRY,in_mspace_prod_measure_space,GSYM CONJ_ASSOC,SF SFY_ss]) >>
    pop_assum kall_tac >> simp[LAMBDA_PROD] >> drule_all_then assume_tac in_measurable_borel_hsans_hist_lst_pdf >>
    pop_assum $ qspec_then `n` $ assume_tac o SIMP_RULE (srw_ss ()) [ELIM_UNCURRY_PAIRARG] >>
    fs[valid_dist_gen_funs_def] >> simp[traj_m_space_n_hist_m_space_n,traj_state_n_in_m_space,SF SFY_ss] >>
    rpt $ qpat_x_assum `∀x. _` kall_tac >> qpat_x_assum `prob_space _` kall_tac >>
    (* post tree depth 1 *)
    `(λ(h,w,a,r). hcons h w a r) ∈ measurable (sig_alg (hist_measure_space_n n m_o m_a m_r × m_o × m_a × m_r))
      (sig_alg (hist_measure_space_n (SUC n) m_o m_a m_r))` by (
        resolve_then Any irule in_measure_preserving_hcons measure_preserving_measurable >> simp[]) >>
    fs[sig_alg_prod_measure_space] >>
    NTAC 4 $ last_x_assum $ C (resolve_then Any assume_tac) sigma_finite_measure_space_measure_space >>
    map_every qabbrev_tac [`hspdf = hist_lst_pdf m_s d0 P Z R bet`,
        `sa_t = traj_sig_alg_n n m_s m_o m_a m_r`,`sa_h = hist_sig_alg_n n m_o m_a m_r`,
        `sa_o = sig_alg m_o`,`sa_a = sig_alg m_a`,`sa_s = sig_alg m_s`,`sa_r = sig_alg m_r`] >>
    `t_hist ∈ measurable sa_t sa_h ∧ t_st ∈ measurable sa_t sa_s` by (simp[Abbr `sa_t`,Abbr `sa_h`,Abbr `sa_s`] >>
        map_every (irule_at Any) [in_measurable_traj_hist,traj_state_measurable] >> simp[]) >>
    `sigma_algebra sa_t ∧ sigma_algebra sa_h` by (simp[Abbr `sa_t`,Abbr `sa_h`] >>
        simp[sigma_algebra_traj_sig_alg_n,sigma_algebra_hist_sig_alg_n]) >>
    `t_hist ∈ measurable sa_t sa_h ∧ t_st ∈ measurable sa_t sa_s` by 
        simp[Abbr `sa_t`,Abbr `sa_h`,Abbr `sa_s`,in_measurable_traj_hist,traj_state_measurable] >>
    `sigma_algebra sa_t ∧ sigma_algebra sa_h` by
        simp[Abbr `sa_t`,Abbr `sa_h`,sigma_algebra_traj_sig_alg_n,sigma_algebra_hist_sig_alg_n] >>
    NTAC 4 $ last_x_assum $ C (resolve_then Any assume_tac) $ cj 1 MEASURE_SPACE_SIGMA_ALGEBRA >> rfs[] >>
    `(λ(j,w,a,t,r). (t_hist j,t_st j,w,a,t,r)) ∈
      measurable (sa_t × sa_o × sa_a × sa_s × sa_r) (sa_h × sa_s × sa_o × sa_a × sa_s × sa_r) ∧
      (λ((h,s),w,a,t,r). (h,s,w,a,t,r)) ∈ measurable
      ((sa_h × sa_s) × sa_o × sa_a × sa_s × sa_r) (sa_h × sa_s × sa_o × sa_a × sa_s × sa_r) ∧
      (λ(h,s,w,a,t,r). Z s w * bet w a * P s a t * R s a t r * f (hcons h w a r,t)) ∈
      Borel_measurable (sa_h × sa_s × sa_o × sa_a × sa_s × sa_r) ∧
      (λ(h,s,w,a,t,r). hspdf h s) ∈ Borel_measurable (sa_h × sa_s × sa_o × sa_a × sa_s × sa_r) ∧
      (λ(h,s,w,a,t,r). Z s w * P s a t * R s a t r) ∈
      Borel_measurable (sa_h × sa_s × sa_o × sa_a × sa_s × sa_r)` by (fs[sig_alg_prod_measure_space] >>
        map_every (fn (n,qex) => irule_at (Pos $ el n) IN_MEASURABLE_BOREL_MUL' >>
            qexistsl_tac qex >> csimp[FORALL_PROD,mul_assoc]) [
            (5,[`λ(h,s,w,a,t,r). P s a t * R s a t r`,`λ(h,s,w,a,t,r). Z s w`]),
            (6,[`λ(h,s,w,a,t,r). bet w a * P s a t * R s a t r * f (hcons h w a r,t)`,`λ(h,s,w,a,t,r). Z s w`]),
            (1,[`λ(h,s,w,a,t,r). P s a t * R s a t r * f (hcons h w a r,t)`,`λ(h,s,w,a,t,r). bet w a`]),
            (2,[`λ(h,s,w,a,t,r). f (hcons h w a r,t)`,`λ(h,s,w,a,t,r). P s a t * R s a t r`]),
            (5,[`λ(h,s,w,a,t,r). R s a t r`,`λ(h,s,w,a,t,r). P s a t`])] >>
        last_x_assum kall_tac >>
        let fun tacf tm = last_x_assum $ C (resolve_then (Pos $ el 2) (qspec_then tm (irule_at Any o
            SIMP_RULE (srw_ss ()) [Once $ GSYM LAMBDA_PROD] o
            SIMP_RULE (srw_ss ()) [o_DEF,LAMBDA_PROD]))) MEASURABLE_COMP in
            map_every tacf [`λ(h,s,w,a,t,r). (s,a,t)`,`λ(h,s,w,a,t,r). (s,w)`,`λ(h,s,w,a,t,r). (s,a,t,r)`,
                `λ(h,s,w,a,t,r). (w,a)`,`λ(h,s,w,a,t,r). (h,s)`,`λ(h,s,w,a,t,r). (hcons h w a r,t)`] >>
            irule_at (Pos hd) MEASURABLE_PROD_SIGMA' >> simp[o_DEF,LAMBDA_PROD] >>
            tacf `λ(h,s,w,a,t,r). (h,w,a,r)` >>
            rpt $ irule_at Any MEASURABLE_PROD_SIGMA' >> csimp[o_DEF,LAMBDA_PROD] >>
            map_every tacf [`λ(j,w,a,t,r). j`,`λ(j,w,a,t,r). j`] end >>
        `sigma_algebra (sa_h × sa_s × sa_o × sa_a × sa_s × sa_r) ∧
          sigma_algebra (sa_t × sa_o × sa_a × sa_s × sa_r) ∧
          sigma_algebra ((sa_h × sa_s) × sa_o × sa_a × sa_s × sa_r)` by (
            rpt $ irule_at Any SIGMA_ALGEBRA_PROD_SIGMA_WEAK >> simp[]) >>
        NTAC 3 $ dxrule_then assume_tac MEASURABLE_I >>
        NTAC 14 $ first_x_assum (fn th => map_every
            (C (resolve_then (Pos $ el 2) (resolve_then Any assume_tac th)) MEASURABLE_COMP)
            [IN_MEASURABLE_FST,IN_MEASURABLE_SND]) >>
        rfs[o_DEF,LAMBDA_PROD,Excl "I_o_ID"] >> rpt $ pop_assum $ irule_at Any >>
        rpt $ irule_at Any SIGMA_ALGEBRA_PROD_SIGMA_WEAK >> simp[]) >>
    simp[GSYM space_traj_sig_alg,GSYM space_hist_sig_alg,GSYM space_sig_alg,
        Excl "space_traj_sig_alg",Excl "space_hist_sig_alg",Excl "space_sig_alg"] >>
    NTAC 17 $ last_x_assum kall_tac >>
    pop_assum $ C (resolve_then (Pos $ el 3) $ first_assum o
        C (resolve_then Any $ qspec_then `λ(h,s,w,a,t,r). hspdf h s * Z s w * P s a t * R s a t r` $
        (C (resolve_then Any $ C (resolve_then Any mp_tac) $
        cj 1 IN_MEASURABLE_BOREL_FROM_PROD_SIGMA_ALT) $ cj 2 IN_MEASURABLE_BOREL_FROM_PROD_SIGMA_ALT) o
        SIMP_RULE (srw_ss ()) [FORALL_PROD,mul_assoc])) IN_MEASURABLE_BOREL_MUL' >>
    (* post tree depth 2 *)
    rpt $ ConseqConv.CONSEQ_REWRITE_TAC ([SIGMA_ALGEBRA_PROD_SIGMA_WEAK],[],[]) >>
    simp[FORALL_PROD,LAMBDA_PROD,SPACE_PROD_SIGMA] >> DISCH_THEN kall_tac >>
    pop_assum $ C (resolve_then (Pos $ el 2) $ first_assum o C (resolve_then Any $
        qspec_then `λ(h,s,w,a,t,r). hspdf h s * Z s w * bet w a * P s a t * R s a t r * f (hcons h w a r,t)` $
        mp_tac o SIMP_RULE (srw_ss ()) [FORALL_PROD,mul_assoc])) IN_MEASURABLE_BOREL_MUL' >>
    rpt $ ConseqConv.CONSEQ_REWRITE_TAC ([SIGMA_ALGEBRA_PROD_SIGMA_WEAK],[],[]) >> simp[] >> strip_tac >>
    NTAC 2 $ last_x_assum $ C (resolve_then Any (imp_res_tac)) MEASURABLE_COMP >>
    fs[o_DEF,LAMBDA_PROD] >>
    NTAC 6 $ last_x_assum $ C (resolve_then (Pos $ el 3) assume_tac) $
        cj 2 IN_MEASURABLE_BOREL_FROM_PROD_SIGMA_ALT >>
    rfs[SIGMA_ALGEBRA_PROD_SIGMA_WEAK,SPACE_PROD_SIGMA,GSYM PFORALL_THM,LAMBDA_PROD]
QED

Theorem prob_space_hist_measure_space_n_pdf:
    ∀n (m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space) d0 P Z R bet.
       sigma_finite_measure_space m_s ∧ sigma_finite_measure_space m_o ∧
       sigma_finite_measure_space m_a ∧ sigma_finite_measure_space m_r ∧
       valid_dist_gen_funs m_s m_o m_a m_r d0 P Z R bet ⇒
       prob_space (density (hist_measure_space_n n m_o m_a m_r) (hist_pdf m_s d0 P Z R bet))
Proof
    rw[] >> drule_all_then mp_tac prob_space_traj_measure_space_n_pdf >>
    simp[prob_space_alt] >> DISCH_THEN $ qspec_then `n` $ assume_tac o cj 2 >>
    irule_at Any measure_space_density >>
    simp[measure_space_hist_measure_space_n,hist_pdf_n_pos,in_measurable_borel_hsan_hist_pdf,SF SFY_ss] >>
    pop_assum mp_tac >> qmatch_abbrev_tac `_ dmt _ = _ ⇒ _ dmh _ = _` >>
    `∫⁺ dmt ((λx. 1) ∘ t_hist) = ∫⁺ dmh (λx. 1)` suffices_by simp[o_DEF] >>
    UNABBREV_ALL_TAC >> irule traj_pos_fn_integral_hist_pos_fn_integral >> simp[] >>
    irule IN_MEASURABLE_BOREL_CONST' >> simp[sigma_algebra_hist_sig_alg_n]
QED

(* Theorem 1 Part 1 *)

Theorem hist_ir_n_pos:
    ∀n (m_s: σ m_space) m_o m_a m_r d0 P Z R bet phi (h: (α,ρ,ω) hist).
        valid_dist_gen_funs m_s m_o m_a m_r d0 P Z R bet ∧
        valid_dist_gen_funs m_s m_o m_a m_r d0 P Z R phi ∧
        (∀w a. w ∈ m_space m_o ∧ a ∈ m_space m_a ∧ bet w a = 0 ⇒ phi w a = 0) ∧
        h ∈ hist_m_space_n n m_o m_a m_r ⇒ 0 ≤ h_importance_ratio phi bet h
Proof
    Induct_on `n` >> rpt gen_tac >> Cases_on `h` >> simp[in_hist_m_space_n,h_importance_ratio_def] >>
    rw[] >> last_x_assum $ drule_all_then assume_tac >> simp[Once $ GSYM mul_assoc] >> irule le_mul >>
    simp[] >> rename [`0 ≤ phi w a * _`] >> Cases_on `bet w a = 0` >> simp[] >> irule le_mul >>
    fs[valid_dist_gen_funs_def] >> irule le_inv >> simp[lt_le]
QED

Theorem hist_ir_n_not_infty:
    ∀n (m_s: σ m_space) m_o m_a m_r d0 P Z R bet phi (h: (α,ρ,ω) hist).
        valid_dist_gen_funs m_s m_o m_a m_r d0 P Z R bet ∧
        valid_dist_gen_funs m_s m_o m_a m_r d0 P Z R phi ∧
        (∀w a. w ∈ m_space m_o ∧ a ∈ m_space m_a ∧ bet w a = 0 ⇒ phi w a = 0) ∧
        h ∈ hist_m_space_n n m_o m_a m_r ⇒ h_importance_ratio phi bet h ≠ +∞
Proof
    Induct_on `n` >> rpt gen_tac >> Cases_on `h` >> simp[in_hist_m_space_n,h_importance_ratio_def] >>
    rw[] >> rename [`_ _ _ h * _ w a * _`] >> last_x_assum $ drule_at_then (Pos $ el 3) assume_tac >>
    NTAC 3 $ pop_assum $ drule_then assume_tac >> Cases_on `bet w a = 0` >> simp[] >>
    NTAC 2 $ irule_at Any $ cj 2 mul_not_infty2 >> irule_at Any $ cj 1 mul_not_infty2 >>
    simp[inv_not_infty] >> NTAC 2 $ irule_at Any pos_not_neginf >>
    drule_all_then assume_tac hist_ir_n_pos >> simp[] >> fs[valid_dist_gen_funs_def]
QED

Theorem opehir_pos_fn:
    ∀n (m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space) d0 P Z R bet phi f.
        sigma_finite_measure_space m_s ∧ sigma_finite_measure_space m_o ∧
        sigma_finite_measure_space m_a ∧ sigma_finite_measure_space m_r ∧
        valid_dist_gen_funs m_s m_o m_a m_r d0 P Z R bet ∧
        valid_dist_gen_funs m_s m_o m_a m_r d0 P Z R phi ∧
        (∀w a. w ∈ m_space m_o ∧ a ∈ m_space m_a ∧ bet w a = 0 ⇒ phi w a = 0) ∧
        f ∈ Borel_measurable (hist_sig_alg_n n m_o m_a m_r) ∧
        (∀x. x ∈ hist_m_space_n n m_o m_a m_r ⇒ 0 ≤ f x) ⇒
        ∫⁺ (density (traj_measure_space_n n m_s m_o m_a m_r) (traj_pdf d0 P Z R phi)) (f ∘ t_hist) =
        ∫⁺ (density (hist_measure_space_n n m_o m_a m_r) (hist_pdf m_s d0 P Z R bet))
        (λh. h_importance_ratio phi bet h * f h)
Proof
    rw[] >>
    resolve_then Any (resolve_then (Pos $ el 3)
        (resolve_then Any irule opeir_pos_fn)
        traj_pos_fn_integral_hist_pos_fn_integral) EQ_TRANS EQ_TRANS >>
    simp[GSYM RIGHT_EXISTS_AND_THM] >> qexists_tac `bet` >>
    ConseqConv.CONSEQ_REWRITE_TAC ([le_mul],[],[]) >>
    drule_then (fn th => ConseqConv.CONSEQ_REWRITE_TAC ([th],[],[])) hist_ir_n_pos >> simp[SF SFY_ss] >>
    first_assum $ (fn th => ConseqConv.CONSEQ_REWRITE_TAC ([th],[],[])) >>
    simp[traj_m_space_n_hist_m_space_n,SF SFY_ss] >>
    irule_at Any MEASURABLE_COMP >> irule_at (Pos $ el 3) IN_MEASURABLE_BOREL_MUL' >>
    qexistsl_tac [`f`,`h_importance_ratio phi bet`,`hist_sig_alg_n n m_o m_a m_r`] >>
    simp[traj_importance_ratio_alt,o_DEF,sigma_algebra_hist_sig_alg_n,
        in_measurable_borel_hsan_importance_ratio,in_measurable_traj_hist,SF SFY_ss]
QED

Theorem opehir:
    ∀n (m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space) d0 P Z R bet phi f.
        sigma_finite_measure_space m_s ∧ sigma_finite_measure_space m_o ∧
        sigma_finite_measure_space m_a ∧ sigma_finite_measure_space m_r ∧
        valid_dist_gen_funs m_s m_o m_a m_r d0 P Z R bet ∧
        valid_dist_gen_funs m_s m_o m_a m_r d0 P Z R phi ∧
        (∀w a. w ∈ m_space m_o ∧ a ∈ m_space m_a ∧ bet w a = 0 ⇒ phi w a = 0) ∧
        f ∈ Borel_measurable (hist_sig_alg_n n m_o m_a m_r) ⇒
        ∫ (density (traj_measure_space_n n m_s m_o m_a m_r) (traj_pdf d0 P Z R phi)) (f ∘ t_hist) =
        ∫ (density (hist_measure_space_n n m_o m_a m_r) (hist_pdf m_s d0 P Z R bet))
        (λh. h_importance_ratio phi bet h * f h)
Proof
    rw[integral_def] >> `∀x1:extreal x2 x3 x4. x1 = x3 ∧ x2 = x4 ⇒ x1 - x2 = x3 - x4` by simp[] >>
    `(f ∘ t_hist)⁺ : (α,ρ,σ,ω) traj -> extreal = f⁺ ∘ t_hist ∧
      (f ∘ t_hist)⁻ : (α,ρ,σ,ω) traj -> extreal = f⁻ ∘ t_hist` by simp[o_DEF,fn_plus_def,fn_minus_def] >>
    map_every pop_assum [SUBST1_TAC,SUBST1_TAC,irule] >>
    NTAC 2 $ resolve_then (Pos $ el 1) (irule_at $ Pos last) opehir_pos_fn EQ_TRANS >>
    qexistsl_tac [`bet`,`bet`] >> NTAC 2 $ resolve_then Any (irule_at Any) pos_fn_integral_cong EQ_SYM >>
    csimp[iffLR IN_MEASURABLE_BOREL_PLUS_MINUS,FN_PLUS_POS,FN_MINUS_POS] >>
    irule_at Any measure_space_density >>
    simp[hist_pdf_n_pos,in_measurable_borel_hsan_hist_pdf,measure_space_hist_measure_space_n,SF SFY_ss] >>
    simp[GSYM FORALL_IMP_CONJ_THM] >> qx_gen_tac `h` >> DISCH_TAC >>
    `0 ≤ h_importance_ratio phi bet h` by (drule_all_then mp_tac hist_ir_n_pos >> simp[]) >>
    simp[le_mul,FN_PLUS_POS,FN_MINUS_POS] >>
    map_every (drule_then (mp_tac o Q.SPEC `f`) o cj 1 o INST_TYPE [``:α`` |-> ``:(α,ρ,ω) hist``])
        [FN_PLUS_CMUL_full,FN_MINUS_CMUL_full] >>
    simp[FUN_EQ_THM,fn_plus_def,fn_minus_def]
QED

Theorem opehir_integrable:
    ∀n (m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space) d0 P Z R bet phi f.
        sigma_finite_measure_space m_s ∧ sigma_finite_measure_space m_o ∧
        sigma_finite_measure_space m_a ∧ sigma_finite_measure_space m_r ∧
        valid_dist_gen_funs m_s m_o m_a m_r d0 P Z R bet ∧
        valid_dist_gen_funs m_s m_o m_a m_r d0 P Z R phi ∧
        (∀w a. w ∈ m_space m_o ∧ a ∈ m_space m_a ∧ bet w a = 0 ⇒ phi w a = 0) ∧
        integrable (density (hist_measure_space_n n m_o m_a m_r) (hist_pdf m_s d0 P Z R phi)) f ⇒
        integrable (density (hist_measure_space_n n m_o m_a m_r) (hist_pdf m_s d0 P Z R bet))
        (λh. h_importance_ratio phi bet h * f h)
Proof
    rw[] >> fs[integrable_def] >> `∀x:extreal y z. x = y ∧ x ≠ z ⇒ y ≠ z` by simp[] >>
    pop_assum $ NTAC 2 o pop_assum o C (resolve_then Any (irule_at $ Pos last)) >>
    irule_at Any IN_MEASURABLE_BOREL_MUL' >> qexistsl_tac [`f`,`h_importance_ratio phi bet`] >>
    simp[sigma_algebra_hist_sig_alg_n,in_measurable_borel_hsan_importance_ratio,SF SFY_ss] >>
    NTAC 2 $ resolve_then Any (resolve_then (Pos $ el 2) (resolve_then Any (irule_at $ Pos last) $
        GSYM traj_pos_fn_integral_hist_pos_fn_integral) opehir_pos_fn) EQ_TRANS EQ_TRANS >>
    qexistsl_tac [`bet`,`bet`] >> NTAC 2 $ resolve_then Any (irule_at Any) pos_fn_integral_cong EQ_SYM >>
    csimp[iffLR IN_MEASURABLE_BOREL_PLUS_MINUS,FN_PLUS_POS,FN_MINUS_POS] >>
    irule_at Any measure_space_density >>
    simp[hist_pdf_n_pos,in_measurable_borel_hsan_hist_pdf,measure_space_hist_measure_space_n,SF SFY_ss] >>
    simp[GSYM FORALL_IMP_CONJ_THM] >> qx_gen_tac `h` >> DISCH_TAC >>
    `0 ≤ h_importance_ratio phi bet h` by (drule_all_then mp_tac hist_ir_n_pos >> simp[]) >>
    simp[le_mul,FN_PLUS_POS,FN_MINUS_POS] >>
    map_every (drule_then (mp_tac o Q.SPEC `f`) o cj 1 o INST_TYPE [``:α`` |-> ``:(α,ρ,ω) hist``])
        [FN_PLUS_CMUL_full,FN_MINUS_CMUL_full] >>
    simp[FUN_EQ_THM,fn_plus_def,fn_minus_def]
QED

Theorem opehir_traj_ret_cdf:
    ∀n (m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: extreal m_space) d0 P Z R bet phi g c.
        sigma_finite_measure_space m_s ∧ sigma_finite_measure_space m_o ∧
        sigma_finite_measure_space m_a ∧ sigma_finite_measure_space m_r ∧ sig_alg m_r = Borel ∧
        valid_dist_gen_funs m_s m_o m_a m_r d0 P Z R bet ∧
        valid_dist_gen_funs m_s m_o m_a m_r d0 P Z R phi ∧
        (∀w a. w ∈ m_space m_o ∧ a ∈ m_space m_a ∧ bet w a = 0 ⇒ phi w a = 0) ⇒
        traj_ret_cdf n m_s m_o m_a m_r d0 P Z R phi g c =
        ∫ (density (hist_measure_space_n n m_o m_a m_r) (hist_pdf m_s d0 P Z R bet))
        (λh. h_importance_ratio phi bet h * 𝟙 {h | hist_return g h ≤ c} h)
Proof
    rw[] >> drule_all_then assume_tac opeir_traj_ret_cdf >> simp[] >> pop_assum kall_tac >>
    qmatch_abbrev_tac `_ dmt ft = _ dmh fh` >>
    `∫ dmt ft = ∫⁺ dmt ft ∧ ∫ dmh fh = ∫⁺ dmh fh ∧ ∫⁺ dmt (fh ∘ t_hist) = ∫⁺ dmt ft ∧
        ∫⁺ dmt (fh ∘ t_hist) = ∫⁺ dmh fh` suffices_by (rw[] >> pop_assum $ SUBST1_TAC o SYM >> simp[]) >>
    NTAC 2 $ irule_at Any integral_pos_fn >> irule_at Any pos_fn_integral_cong >> csimp[] >>
    UNABBREV_ALL_TAC >> irule_at Any traj_pos_fn_integral_hist_pos_fn_integral >> csimp[] >>
    map_every (fn (pos,tm,qex,ths) => irule_at pos tm >> qexistsl_tac qex >> simp ths) [
        (Pos (el 3),measure_space_density,[],
            [measure_space_hist_measure_space_n,in_measurable_borel_hsan_hist_pdf,hist_pdf_n_pos,SF SFY_ss]),
        (Pos (el 4),measure_space_density,[],
            [measure_space_traj_measure_space_n,in_measurable_borel_tsan_traj_pdf,traj_pdf_n_pos,SF SFY_ss]),
        (Any,IN_MEASURABLE_BOREL_MUL',[`𝟙 {h | hist_return g h ≤ c}`,`h_importance_ratio phi bet`],
            [in_measurable_borel_hsan_importance_ratio,SF SFY_ss]),
        (Any,IN_MEASURABLE_BOREL_INDICATOR,[`{h | hist_return g h ≤ c} ∩ space (hist_sig_alg_n n m_o m_a m_r)`],
            [Excl "space_hist_sig_alg",Excl "subsets_hist_sig_alg",Ntimes indicator_fn_def 2]),
        (Any,IN_MEASURABLE_BOREL_RC,[],[sigma_algebra_hist_sig_alg_n,in_measurable_borel_hsan_hist_return])] >>
    CONJ_TAC >- simp[traj_importance_ratio_alt,traj_return_alt,indicator_fn_def] >>
    rw[] >> irule le_mul >> simp[INDICATOR_FN_POS] >| [irule hist_ir_n_pos,irule traj_ir_n_pos] >>
    qexistsl_tac [`P`,`R`,`Z`,`d0`,`m_a`,`m_o`,`m_r`,`m_s`,`n`] >> simp[]
QED

Definition data_ret_cdf_def:
    data_ret_cdf n (phi: ω -> α -> extreal) beti hi g c = (&n)⁻¹ *
        ∑ (λi. h_importance_ratio phi (beti i) (hi i) * 𝟙 {h | hist_return g h ≤ c} (hi i)) (count n)
End

val _ = augment_srw_ss [PI_MSP_ss];

Theorem opedbir_pos_fn:
    ∀nD nT (m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space) d0 P Z R beti phi f.
        0 < nD ∧ sigma_finite_measure_space m_s ∧ sigma_finite_measure_space m_o ∧
        sigma_finite_measure_space m_a ∧ sigma_finite_measure_space m_r ∧
        (∀i. i < nD ⇒ valid_dist_gen_funs m_s m_o m_a m_r d0 P Z R (beti i)) ∧
        valid_dist_gen_funs m_s m_o m_a m_r d0 P Z R phi ∧
        (∀i w a. i < nD ∧ w ∈ m_space m_o ∧ a ∈ m_space m_a ∧ (beti i) w a = 0 ⇒ phi w a = 0) ∧
        f ∈ Borel_measurable (hist_sig_alg_n nT m_o m_a m_r) ∧
        (∀x. x ∈ hist_m_space_n nT m_o m_a m_r ⇒ 0 ≤ f x) ⇒
        ∫⁺ (pi_measure_space nD (λi. density (hist_measure_space_n nT m_o m_a m_r) (hist_pdf m_s d0 P Z R (beti i))))
        (λhi. (&nD)⁻¹ * ∑ (λi. h_importance_ratio phi (beti i) (hi i) * f (hi i)) (count nD)) =
        ∫⁺ (density (traj_measure_space_n nT m_s m_o m_a m_r) (traj_pdf d0 P Z R phi)) (f ∘ t_hist)
Proof
    rw[] >> qabbrev_tac `hirfi = (λi h. h_importance_ratio phi (beti i) h * f h)` >>
    qabbrev_tac `dhmi = (λi. density (hist_measure_space_n nT m_o m_a m_r) (hist_pdf m_s d0 P Z R (beti i)))` >>
    `∀i. i < nD ⇒ prob_space (dhmi i)` by simp[Abbr `dhmi`,prob_space_hist_measure_space_n_pdf,SF SFY_ss] >>
    `measure_space (pi_measure_space nD dhmi)` by (irule measure_space_pi_measure_space >>
        simp[prob_space_sigma_finite_measure_space]) >>
    `∀i h. i < nD ∧ h ∈ hist_m_space_n nT m_o m_a m_r ⇒ 0 ≤ hirfi i h` by (rw[Abbr `hirfi`] >>
        irule le_mul >> simp[INDICATOR_FN_POS] >> irule hist_ir_n_pos >>
        qexistsl_tac [`P`,`R`,`Z`,`d0`,`m_a`,`m_o`,`m_r`,`m_s`,`nT`] >> simp[SF SFY_ss]) >>
    `∀hi. hi ∈ pi_m_space nD dhmi ⇒ 0 ≤ ∑ (λi. hirfi i (hi i)) (count nD)` by (rw[] >>
        irule EXTREAL_SUM_IMAGE_POS >> simp[] >> rw[] >>
        drule_all_then assume_tac in_pi_m_space_in_m_space >> fs[Abbr `dhmi`]) >>
    irule EQ_TRANS >>
    qexists_tac `∫⁺ (pi_measure_space nD dhmi) (λhi. (&nD)⁻¹ * ∑ (λi. hirfi i (hi i)) (count nD))` >>
    CONJ_TAC >- (qunabbrev_tac `hirfi` >> simp[]) >>
    qspecl_then [`pi_measure_space nD dhmi`,`λhi. ∑ (λi. hirfi i (hi i)) (count nD)`,`(&nD)⁻¹`]
        mp_tac pos_fn_integral_cmul >>
    simp[GSYM extreal_inv_def,GSYM extreal_of_num_def] >> DISCH_THEN kall_tac >> irule EQ_TRANS >>
    qexists_tac ` (&nD)⁻¹ * ∑ (λi. ∫⁺ (dhmi i) (hirfi i)) (count nD)` >> CONJ_TAC
    >- (irule IRULER >> irule pos_fn_integral_pi_sum_dim >> UNABBREV_ALL_TAC >> simp[] >>
        NTAC 4 $ pop_assum kall_tac >> qx_gen_tac `i` >> DISCH_TAC >>
        irule IN_MEASURABLE_BOREL_MUL' >> simp[sigma_algebra_hist_sig_alg_n] >>
        qexistsl_tac [`h_importance_ratio phi (beti i)`,`f`] >> simp[] >>
        qspecl_then [`nT`,`m_s`,`m_o`,`m_a`,`m_r`,`d0`,`P`,`Z`,`R`,`beti i`,`phi`]
            mp_tac in_measurable_borel_hsan_importance_ratio >> simp[SF SFY_ss]) >>
    irule EQ_TRANS >>
    qexists_tac ` (&nD)⁻¹ * (&CARD (count nD) *
        ∫⁺ (density (traj_measure_space_n nT m_s m_o m_a m_r) (traj_pdf d0 P Z R phi)) (f ∘ t_hist))` >>
    REVERSE CONJ_TAC
    >- (simp[mul_assoc] >> `(&nD)⁻¹ * &nD = 1` suffices_by simp[] >> irule mul_linv >> simp[extreal_of_num_def]) >>
    irule IRULER >> irule EXTREAL_SUM_IMAGE_FINITE_CONST >> simp[] >> qx_gen_tac `i`  >> DISCH_TAC >>
    UNABBREV_ALL_TAC >> simp[] >> irule $ GSYM opehir_pos_fn >> simp[SF SFY_ss]
QED

Theorem opedbir:
    ∀nD nT (m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space) d0 P Z R beti phi f.
        0 < nD ∧ sigma_finite_measure_space m_s ∧ sigma_finite_measure_space m_o ∧
        sigma_finite_measure_space m_a ∧ sigma_finite_measure_space m_r ∧
        (∀i. i < nD ⇒ valid_dist_gen_funs m_s m_o m_a m_r d0 P Z R (beti i)) ∧
        valid_dist_gen_funs m_s m_o m_a m_r d0 P Z R phi ∧
        (∀i w a. i < nD ∧ w ∈ m_space m_o ∧ a ∈ m_space m_a ∧ (beti i) w a = 0 ⇒ phi w a = 0) ∧
        integrable (density (hist_measure_space_n nT m_o m_a m_r) (hist_pdf m_s d0 P Z R phi)) f ⇒
        ∫ (pi_measure_space nD (λi. density (hist_measure_space_n nT m_o m_a m_r) (hist_pdf m_s d0 P Z R (beti i))))
        (λhi. (&nD)⁻¹ * ∑ (λi. h_importance_ratio phi (beti i) (hi i) * f (hi i)) (count nD)) =
        ∫ (density (traj_measure_space_n nT m_s m_o m_a m_r) (traj_pdf d0 P Z R phi)) (f ∘ t_hist)
Proof
    rw[] >> qabbrev_tac `hirfi = (λi h. h_importance_ratio phi (beti i) h * f h)` >>
    qabbrev_tac `dhmi = (λi. density (hist_measure_space_n nT m_o m_a m_r) (hist_pdf m_s d0 P Z R (beti i)))` >>
    `∀i. i < nD ⇒ prob_space (dhmi i)` by simp[Abbr `dhmi`,prob_space_hist_measure_space_n_pdf,SF SFY_ss] >>
    `∀i. i < nD ⇒ integrable (dhmi i) (hirfi i)` by (UNABBREV_ALL_TAC >> rw[] >>
        irule opehir_integrable >> simp[SF SFY_ss]) >>
    `measure_space (pi_measure_space nD dhmi)` by (irule measure_space_pi_measure_space >>
        simp[prob_space_sigma_finite_measure_space]) >>
    dxrule_then assume_tac integrable_measurable >> fs[] >> irule EQ_TRANS >>
    qexists_tac `∫ (pi_measure_space nD dhmi) (λhi. (&nD)⁻¹ * ∑ (λi. hirfi i (hi i)) (count nD))` >>
    CONJ_TAC >- (qunabbrev_tac `hirfi` >> simp[]) >>
    qspecl_then [`pi_measure_space nD dhmi`,`λhi. ∑ (λi. hirfi i (hi i)) (count nD)`,`(&nD)⁻¹`]
        mp_tac integral_cmul >>
    drule_all_then assume_tac integrable_pi_sum_dim >>
    simp[GSYM extreal_inv_def,GSYM extreal_of_num_def,integral_pi_sum_dim] >> DISCH_THEN kall_tac >>
    irule EQ_TRANS >>
    qexists_tac ` (&nD)⁻¹ * (&CARD (count nD) *
        ∫ (density (traj_measure_space_n nT m_s m_o m_a m_r) (traj_pdf d0 P Z R phi)) (f ∘ t_hist))` >>
    REVERSE CONJ_TAC
    >- (simp[mul_assoc] >> `(&nD)⁻¹ * &nD = 1` suffices_by simp[] >> irule mul_linv >> simp[extreal_of_num_def]) >>
    irule IRULER >> irule EXTREAL_SUM_IMAGE_FINITE_CONST >> simp[] >> qx_gen_tac `i`  >> DISCH_TAC >>
    UNABBREV_ALL_TAC >> simp[] >> irule $ GSYM opehir >> simp[SF SFY_ss]
QED

Theorem opedbir_integrable:
    ∀nD nT (m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space) d0 P Z R beti phi f.
        0 < nD ∧ sigma_finite_measure_space m_s ∧ sigma_finite_measure_space m_o ∧
        sigma_finite_measure_space m_a ∧ sigma_finite_measure_space m_r ∧
        (∀i. i < nD ⇒ valid_dist_gen_funs m_s m_o m_a m_r d0 P Z R (beti i)) ∧
        valid_dist_gen_funs m_s m_o m_a m_r d0 P Z R phi ∧
        (∀i w a. i < nD ∧ w ∈ m_space m_o ∧ a ∈ m_space m_a ∧ (beti i) w a = 0 ⇒ phi w a = 0) ∧
        integrable (density (hist_measure_space_n nT m_o m_a m_r) (hist_pdf m_s d0 P Z R phi)) f ⇒ integrable
        (pi_measure_space nD (λi. density (hist_measure_space_n nT m_o m_a m_r) (hist_pdf m_s d0 P Z R (beti i))))
        (λhi. (&nD)⁻¹ * ∑ (λi. h_importance_ratio phi (beti i) (hi i) * f (hi i)) (count nD))
Proof
    rw[] >> qabbrev_tac `hirfi = (λi h. h_importance_ratio phi (beti i) h * f h)` >>
    qabbrev_tac `dhmi = (λi. density (hist_measure_space_n nT m_o m_a m_r) (hist_pdf m_s d0 P Z R (beti i)))` >>
    dxrule_at_then (Pos last)
        (qpat_assum `∀i. i < _ ⇒ _` o C (resolve_then Any assume_tac)) opehir_integrable >>
    rfs[GSYM AND_IMP_INTRO,SF ETA_ss,SF SFY_ss] >> fs[AND_IMP_INTRO,GSYM CONJ_ASSOC] >>
    `(&nD)⁻¹ = Normal (&nD)⁻¹` by simp[extreal_of_num_def,extreal_inv_def] >> pop_assum SUBST1_TAC >>
    resolve_then Any (irule o SIMP_RULE (srw_ss ()) []) integrable_pi_sum_dim integrable_cmul >>
    irule_at Any measure_space_pi_measure_space >> csimp[prob_space_sigma_finite_measure_space] >>
    simp[Abbr `dhmi`,prob_space_hist_measure_space_n_pdf,SF SFY_ss]
QED

Definition traj_cdf_def:
    traj_cdf n m_s m_o m_a m_r d0 P Z R bet f (c: extreal) = prob
        (density (traj_measure_space_n n m_s m_o m_a m_r) (traj_pdf d0 P Z R bet))
        ({h:(α,ρ,σ,ω) traj | f h ≤ c} ∩ (traj_m_space_n n m_s m_o m_a m_r))
End

(* put hi at end *)
Definition data_cdf_def:
    data_cdf n (phi: ω -> α -> extreal) beti hi f (c: extreal) = (&n)⁻¹ *
        ∑ (λi. h_importance_ratio phi (beti i) (hi i) * 𝟙 {h | f h ≤ c} (hi i)) (count n)
End

Definition data_return_def:
    data_return n (phi: ω -> α -> extreal) beti g hi = (&n)⁻¹ *
        ∑ (λi. h_importance_ratio phi (beti i) (hi i) * hist_return g (hi i)) (count n)
End

Theorem data_cdf_unbiased:
    ∀nD nT (m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: ρ m_space) d0 P Z R beti phi f c.
        0 < nD ∧ sigma_finite_measure_space m_s ∧ sigma_finite_measure_space m_o ∧
        sigma_finite_measure_space m_a ∧ sigma_finite_measure_space m_r ∧
        (∀i. i < nD ⇒ valid_dist_gen_funs m_s m_o m_a m_r d0 P Z R (beti i)) ∧
        valid_dist_gen_funs m_s m_o m_a m_r d0 P Z R phi ∧
        (∀i w a. i < nD ∧ w ∈ m_space m_o ∧ a ∈ m_space m_a ∧ (beti i) w a = 0 ⇒ phi w a = 0) ∧
        f ∈ Borel_measurable (hist_sig_alg_n nT m_o m_a m_r) ⇒
        expectation (pi_measure_space nD (λi. density (hist_measure_space_n nT m_o m_a m_r)
        (hist_pdf m_s d0 P Z R (beti i)))) (λhi. data_cdf nD phi beti hi f c) =
        traj_cdf nT m_s m_o m_a m_r d0 P Z R phi (f ∘ t_hist) c
Proof
    rw[expectation_def,traj_cdf_def,data_cdf_def,prob_def] >>
    resolve_then Any (resolve_then Any (resolve_then (Pos $ el 2) (resolve_then Any
        (resolve_then (Pos last) (resolve_then Any irule pos_fn_integral_cong)
        pos_fn_integral_indicator) integral_pos_fn) opedbir_pos_fn) EQ_TRANS) EQ_TRANS EQ_TRANS >>
    simp[INDICATOR_FN_POS,SF SFY_ss] >> simp[DROP_INDICATOR_FN] >>
    map_every (fn (pos,tm,qex,ths) => irule_at pos tm >> qexistsl_tac qex >> simp ths) [
        (Any,measure_space_pi_measure_space,[],[]),
        (Any,measure_space_density,[],[measure_space_traj_measure_space_n,in_measurable_borel_tsan_traj_pdf]),
        (Any,IN_MEASURABLE_BOREL_INDICATOR,[`{h | f h ≤ c} ∩ space (hist_sig_alg_n nT m_o m_a m_r)`],
            [Excl "space_hist_sig_alg",Excl "subsets_hist_sig_alg"]),
        (Any,IN_MEASURABLE_BOREL_RC,[],
            [sigma_algebra_hist_sig_alg_n,DROP_INDICATOR_FN,traj_pdf_n_pos,SF SFY_ss]),
        (Any,SIMP_RULE (srw_ss ()) [] $
            Q.SPECL [`f ∘ t_hist`,`traj_sig_alg_n nT m_s m_o m_a m_r`] $
            INST_TYPE [``:α`` |-> ``:(α,ρ,σ,ω) traj``] IN_MEASURABLE_BOREL_RC,[],[]),
        (Any,MEASURABLE_COMP,[`hist_sig_alg_n nT m_o m_a m_r`],[in_measurable_traj_hist])] >>
    CONJ_TAC >> rw[]
    >- (resolve_then Any irule prob_space_hist_measure_space_n_pdf prob_space_sigma_finite_measure_space >>
        simp[]) >>
    irule le_mul >> simp[extreal_of_num_def,extreal_inv_def] >> simp[normal_0,normal_1] >>
    irule EXTREAL_SUM_IMAGE_POS >> simp[FINITE_COUNT] >> rw[] >> rename [`_ phi (beti i) (hi i)`] >>
    irule hist_ir_n_pos >> qexistsl_tac [`P`,`R`,`Z`,`d0`,`m_a`,`m_o`,`m_r`,`m_s`,`nT`] >>
    simp[SF SFY_ss] >> drule_all_then mp_tac in_pi_m_space_in_m_space >> simp[]
QED

Theorem data_ret_cdf_unbaised:
    ∀nD nT (m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: extreal m_space) d0 P Z R beti phi g c.
        0 < nD ∧ sigma_finite_measure_space m_s ∧ sigma_finite_measure_space m_o ∧
        sigma_finite_measure_space m_a ∧ sigma_finite_measure_space m_r ∧ sig_alg m_r = Borel ∧
        (∀i. i < nD ⇒ valid_dist_gen_funs m_s m_o m_a m_r d0 P Z R (beti i)) ∧
        valid_dist_gen_funs m_s m_o m_a m_r d0 P Z R phi ∧
        (∀i w a. i < nD ∧ w ∈ m_space m_o ∧ a ∈ m_space m_a ∧ (beti i) w a = 0 ⇒ phi w a = 0) ⇒
        expectation (pi_measure_space nD (λi. density (hist_measure_space_n nT m_o m_a m_r)
        (hist_pdf m_s d0 P Z R (beti i)))) (λhi. data_ret_cdf nD phi beti hi g c) =
        traj_ret_cdf nT m_s m_o m_a m_r d0 P Z R phi g c
Proof
    rw[expectation_def,data_ret_cdf_def] >>
    qabbrev_tac `dhmi = (λi. density (hist_measure_space_n nT m_o m_a m_r) (hist_pdf m_s d0 P Z R (beti i)))` >>
    qabbrev_tac `hir1i = (λi x. h_importance_ratio phi (beti i) x * 𝟙 {h | hist_return g h ≤ c} x)` >>
    `∀i. i < nD ⇒ prob_space (dhmi i)` by simp[Abbr `dhmi`,prob_space_hist_measure_space_n_pdf,SF SFY_ss] >>
    `measure_space (pi_measure_space nD dhmi)` by (irule measure_space_pi_measure_space >>
        simp[prob_space_sigma_finite_measure_space]) >>
    `∀i h. i < nD ∧ h ∈ hist_m_space_n nT m_o m_a m_r ⇒ 0 ≤ hir1i i h` by (rw[Abbr `hir1i`] >>
        irule le_mul >> simp[INDICATOR_FN_POS] >> irule hist_ir_n_pos >>
        qexistsl_tac [`P`,`R`,`Z`,`d0`,`m_a`,`m_o`,`m_r`,`m_s`,`nT`] >> simp[SF SFY_ss]) >>
    `∀hi. hi ∈ pi_m_space nD dhmi ⇒ 0 ≤ ∑ (λi. hir1i i (hi i)) (count nD)` by (rw[] >>
        irule EXTREAL_SUM_IMAGE_POS >> simp[] >> rw[] >>
        drule_all_then assume_tac in_pi_m_space_in_m_space >> fs[Abbr `dhmi`]) >>
    irule EQ_TRANS >>
    qexists_tac `∫⁺ (pi_measure_space nD dhmi) (λhi. (&nD)⁻¹ * ∑ (λi. hir1i i (hi i)) (count nD))` >>
    CONJ_TAC
    >- (qunabbrev_tac `hir1i` >> simp[] >> irule integral_pos_fn >> simp[] >> qx_gen_tac `hi` >>
        rw[] >> irule le_mul >> irule_at Any le_inv >> fs[extreal_of_num_def]) >>
    qspecl_then [`pi_measure_space nD dhmi`,`λhi. ∑ (λi. hir1i i (hi i)) (count nD)`,`(&nD)⁻¹`]
        mp_tac pos_fn_integral_cmul >>
    simp[GSYM extreal_inv_def,GSYM extreal_of_num_def] >> DISCH_THEN kall_tac >> irule EQ_TRANS >>
    qexists_tac ` (&nD)⁻¹ * ∑ (λi. ∫⁺ (dhmi i) (hir1i i)) (count nD)` >> CONJ_TAC
    >- (irule IRULER >> irule pos_fn_integral_pi_sum_dim >> UNABBREV_ALL_TAC >> simp[] >>
        NTAC 4 $ pop_assum kall_tac >> qx_gen_tac `i` >> DISCH_TAC >> irule IN_MEASURABLE_BOREL_MUL' >>
        fs[sigma_finite_measure_space_def] >> simp[sigma_algebra_hist_sig_alg_n] >>
        qexistsl_tac [`h_importance_ratio phi (beti i)`,`𝟙 {h | hist_return g h ≤ c}`] >> simp[] >>
        qspecl_then [`nT`,`m_s`,`m_o`,`m_a`,`m_r`,`d0`,`P`,`Z`,`R`,`beti i`,`phi`]
            mp_tac in_measurable_borel_hsan_importance_ratio >>
        simp[SF SFY_ss] >> DISCH_THEN kall_tac >>
        irule IN_MEASURABLE_BOREL_INDICATOR >> simp[sigma_algebra_hist_sig_alg_n] >>
        qexists_tac `{h | hist_return g h ≤ c} ∩ hist_m_space_n nT m_o m_a m_r` >> simp[indicator_fn_def] >>
        `hist_return g ∈ Borel_measurable (hist_sig_alg_n nT m_o m_a m_r)`
            by simp[in_measurable_borel_hsan_hist_return] >>
         dxrule_then mp_tac IN_MEASURABLE_BOREL_RC >> simp[]) >>
    irule EQ_TRANS >>
    qexists_tac ` (&nD)⁻¹ * (&CARD (count nD) * traj_ret_cdf nT m_s m_o m_a m_r d0 P Z R phi g c)` >>
    REVERSE CONJ_TAC
    >- (simp[mul_assoc] >> `(&nD)⁻¹ * &nD = 1` suffices_by simp[] >> irule mul_linv >> simp[extreal_of_num_def]) >>
    irule IRULER >> irule EXTREAL_SUM_IMAGE_FINITE_CONST >> simp[] >> qx_gen_tac `i`  >> DISCH_TAC >>
    UNABBREV_ALL_TAC >> simp[] >> irule EQ_SYM >>
    qspecl_then [`nT`,`m_s`,`m_o`,`m_a`,`m_r`,`d0`,`P`,`Z`,`R`,`beti i`,`phi`,`g`,`c`] mp_tac opehir_traj_ret_cdf >>
    simp[SF SFY_ss] >> DISCH_THEN kall_tac >> irule integral_pos_fn >> fs[iffLR prob_space_def]
QED

(* could perhaps require only Gmin ≤ ret ≤ Gmax AE, but AE in what space? *)
Theorem data_return_unbiased:
    ∀nD nT (m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) (m_r: extreal m_space) d0 P Z R beti phi g Gmax Gmin.
        0 < nD ∧ sigma_finite_measure_space m_s ∧ sigma_finite_measure_space m_o ∧
        sigma_finite_measure_space m_a ∧ sigma_finite_measure_space m_r ∧ sig_alg m_r = Borel ∧
        (∀i. i < nD ⇒ valid_dist_gen_funs m_s m_o m_a m_r d0 P Z R (beti i)) ∧
        valid_dist_gen_funs m_s m_o m_a m_r d0 P Z R phi ∧
        (∀i w a. i < nD ∧ w ∈ m_space m_o ∧ a ∈ m_space m_a ∧ (beti i) w a = 0 ⇒ phi w a = 0) ∧
        (∀h. h ∈ hist_m_space_n nT m_o m_a m_r ⇒ Normal Gmin ≤ hist_return g h ∧ hist_return g h ≤ Normal Gmax) ⇒
        expectation (pi_measure_space nD (λi. density (hist_measure_space_n nT m_o m_a m_r)
        (hist_pdf m_s d0 P Z R (beti i)))) (data_return nD phi beti g) =
        expectation (density (traj_measure_space_n nT m_s m_o m_a m_r) (traj_pdf d0 P Z R phi)) (traj_return g)
Proof
    rw[expectation_def] >>
    `data_return nD phi beti g = (λhi. data_return nD phi beti g hi)` by simp[FUN_EQ_THM] >>
    pop_assum SUBST1_TAC >> simp[data_return_def,traj_return_alt] >> irule opedbir >>
    simp[SF SFY_ss] >> irule integrable_bounded_Borel_measurable >>
    resolve_then Any (irule_at Any) prob_space_hist_measure_space_n_pdf prob_space_finite_measure_space >>
    simp[IN_BOUNDED_BOREL_MEASURABLE] >> simp[in_measurable_borel_hsan_hist_return] >>
    qexistsl_tac [`Gmin`,`Gmax`] >> simp[FUNSET,closed_interval_def]
QED

Theorem data_return_ci:
    ∀nD nT (m_s: σ m_space) (m_o: ω m_space) (m_a: α m_space) m_r d0 P Z R beti phi g Gmax Gmin LB UB d.
        0 < nD ∧ 0 < d ∧ sigma_finite_measure_space m_s ∧ sigma_finite_measure_space m_o ∧
        sigma_finite_measure_space m_a ∧ sigma_finite_measure_space m_r ∧ sig_alg m_r = Borel ∧
        (∀i. i < nD ⇒ valid_dist_gen_funs m_s m_o m_a m_r d0 P Z R (beti i)) ∧
        valid_dist_gen_funs m_s m_o m_a m_r d0 P Z R phi ∧
        (∀i w a. i < nD ∧ w ∈ m_space m_o ∧ a ∈ m_space m_a ∧ (beti i) w a = 0 ⇒ phi w a = 0) ∧
        (∀h. h ∈ hist_m_space_n nT m_o m_a m_r ⇒ Normal Gmin ≤ hist_return g h ∧ hist_return g h ≤ Normal Gmax) ∧
        (∀i. i < nD ⇒ AE h::(density (hist_measure_space_n nT m_o m_a m_r) (hist_pdf m_s d0 P Z R (beti i))).
            Normal (LB i) ≤ h_importance_ratio phi (beti i) h * hist_return g h ∧
            h_importance_ratio phi (beti i) h * hist_return g h ≤ Normal (UB i)) ⇒
        Normal (1 − d) ≤ prob
            (pi_measure_space nD (λi. density (hist_measure_space_n nT m_o m_a m_r) (hist_pdf m_s d0 P Z R (beti i))))
            ({hi | data_return nD phi beti g hi -
                Normal (sqrt (ln d⁻¹ * ∑ (λn. (UB n − LB n)²) (count nD) / (2 * (&nD)²))) ≤ expectation
                (density (traj_measure_space_n nT m_s m_o m_a m_r) (traj_pdf d0 P Z R phi)) (traj_return g)} ∩
            pi_m_space nD (λi. density (hist_measure_space_n nT m_o m_a m_r) (hist_pdf m_s d0 P Z R (beti i))))
Proof
    rw[] >> drule_all_then assume_tac data_return_unbiased >> qmatch_abbrev_tac `_ _ (prob p s)` >>
    qspecl_then [`p`,`λi hi. h_importance_ratio phi (beti i) (hi i) * hist_return g (hi i)`,
        `LB`,`UB`,`count nD`,`d`] mp_tac hoeffding_ineq_avg_ci >>
    simp[C_SIMP,GSYM data_return_def,SF ETA_ss] >>
    qpat_x_assum `expectation _ _ = expectation _ _` kall_tac >>
    qunabbrevl_tac [`s`,`p`] >> simp[p_space_def] >> DISCH_THEN irule >>
    irule_at Any prob_space_pi_measure_space >> simp[] >>
    ConseqConv.CONSEQ_REWRITE_TAC ([prob_space_hist_measure_space_n_pdf],[],[]) >> rw[]
    >- (map_every qabbrev_tac
            [`mn = (λn. density (hist_measure_space_n nT m_o m_a m_r) (hist_pdf m_s d0 P Z R (beti n)))`,
            `Q = (λn h. Normal (LB n) ≤ h_importance_ratio phi (beti n) h * hist_return g h ∧
            h_importance_ratio phi (beti n) h * hist_return g h ≤ Normal (UB n))`] >>
        gvs[] >> pop_assum kall_tac >>
        qspecl_then [`nD`,`mn`,`Q`] (dxrule_at Any) pi_measure_space_AE_per_dim >>
        qspecl_then [`pi_measure_space nD mn`,`λhi. ∀i. i < nD ⇒ Q i (hi i)`,`λhi. Q n (hi n)`]
            (DISCH_THEN o C (resolve_then Any irule) o SIMP_RULE (srw_ss ()) []) AE_subset >>
        simp[] >> rw[] >> irule prob_space_sigma_finite_measure_space >>
        qunabbrev_tac `mn` >> simp[prob_space_hist_measure_space_n_pdf])
    >- (rename [‘h_importance_ratio phi (beti n) (_ n)’] >>
        simp[real_random_variable_def,random_variable_def,p_space_def] >>
        irule_at Any $ INST_TYPE
            [``:α`` |-> ``:num -> (α,ρ,ω) hist``,``:β`` |-> ``: (α,ρ,ω) hist``] IN_MEASURABLE_BOREL_COMP >>
        qexistsl_tac [`C LET n`,`λh. h_importance_ratio phi (beti n) h * hist_return g h`,
            `hist_sig_alg_n nT m_o m_a m_r`] >> simp[] >>
        qspecl_then [`nD`,`n`,`density (hist_measure_space_n nT m_o m_a m_r) ∘ hist_pdf m_s d0 P Z R ∘ beti`]
            mp_tac idx_measurable >>
        simp[o_DEF] >> DISCH_THEN $ irule_at Any >> irule_at Any sigma_algebra_pi_sig_alg >> csimp[] >>
        irule_at Any IN_MEASURABLE_BOREL_MUL' >>
        qexistsl_tac [`hist_return g`,`h_importance_ratio phi (beti n)`] >>
        first_assum $ C (resolve_then (Pos $ el 5) $ irule_at Any) in_measurable_borel_hsan_importance_ratio >>
        simp[sigma_algebra_hist_sig_alg_n,in_measurable_borel_hsan_hist_return,SF SFY_ss] >>
        ConseqConv.CONSEQ_REWRITE_TAC ([measure_space_density],[],[]) >>
        simp[measure_space_hist_measure_space_n,in_measurable_borel_hsan_hist_pdf] >> CONJ_TAC
        >- (rw[] >> irule hist_pdf_n_pos >> simp[] >> qexistsl_tac [`m_a`,`m_o`,`m_r`,`nT`] >> simp[]) >>
        qx_gen_tac `hi` >> strip_tac >> drule_all_then assume_tac in_pi_m_space_in_m_space >> fs[] >>
        irule mul_not_infty2 >> simp[] >> irule_at (Pos hd) pos_not_neginf >>
        NTAC 3 $ last_x_assum $ drule_then assume_tac >> gvs[] >>
        (* what the bloody spleen is happening here? *)
        drule_at_then (Pos $ el 1) assume_tac hist_ir_n_not_infty >>
        pop_assum $ drule_at_then (Pos $ el 2) assume_tac >> NTAC 2 $ pop_assum $ drule_then assume_tac >>
        drule_all_then assume_tac hist_ir_n_pos >>
        simp[] >> CCONTR_TAC >> fs[] >> fs[])
    >- (`(λi hi. h_importance_ratio phi (beti i) (hi i) * hist_return g (hi i)) =
            λi. (λi h. h_importance_ratio phi (beti i) h * hist_return g h) i ∘ C LET i` by simp[FUN_EQ_THM] >>
        pop_assum SUBST1_TAC >> irule pi_measure_space_dim_indep_vars >> simp[GSYM FORALL_IMP_CONJ_THM] >>
        qx_gen_tac `i` >> DISCH_TAC >> simp[prob_space_hist_measure_space_n_pdf] >> fs[SF PROB_ss] >>
        irule_at Any IN_MEASURABLE_BOREL_MUL' >> simp[sigma_algebra_hist_sig_alg_n] >>
        qexistsl_tac [`h_importance_ratio phi (beti i)`,`hist_return g`] >>
        first_assum $ C (resolve_then (Pos $ el 5) $ irule_at Any) in_measurable_borel_hsan_importance_ratio >>
        simp[in_measurable_borel_hsan_hist_return,SF SFY_ss])
QED

val _ = export_theory();
