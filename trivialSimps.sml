structure trivialSimps :> trivialSimps = struct

open HolKernel Parse boolLib bossLib;
open simpLib;
open probabilityTheory;
open trivialTheory;

val name_to_thname = fn t => fn s => ({Thy = t, Name = s}, DB.fetch t s);

val PROB_ss = named_rewrites_with_names "PROB" $ map (name_to_thname "probability") [
    "prob_space_def","p_space_def","events_def","prob_def",
    "real_random_variable_def","random_variable_def","expectation_def"];

val TRIVIAL_ss = named_rewrites_with_names "TRIVIAL" $ map (name_to_thname "trivial") [
    "Abbrev_T",
    "extreal_le_simp","extreal_lt_simp","extreal_0_simp",
    "re_sig_alg","sig_alg_tripple","space_sig_alg","subsets_sig_alg",
    "MEASURE_SPACE_SIGMA_ALGEBRA","sigma_finite_measure_space_measure_space",
    "m_space_density","measurable_sets_density","sig_alg_density",
    "prob_re_sig_alg","PROB_SPACE_SIGMA_ALGEBRA"];

val _ = register_frag PROB_ss;

val _ = register_frag TRIVIAL_ss;

end
