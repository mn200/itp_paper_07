structure pispaceSimps :> pispaceSimps = struct

open HolKernel Parse boolLib bossLib;
open simpLib;
open pispaceTheory;

val name_to_thname = fn s => ({Thy = "pispace", Name = s}, DB.fetch "pispace" s);

val PI_MSP_ss = named_rewrites_with_names "PI_MSP" $ map name_to_thname [
    "m_space_pi_measure_space","measurable_sets_pi_measure_space","measure_pi_measure_space",
    "sig_alg_pi_measure_space","space_pi_sig_alg","subsets_pi_sig_alg"];

val _ = register_frag PI_MSP_ss;

end
