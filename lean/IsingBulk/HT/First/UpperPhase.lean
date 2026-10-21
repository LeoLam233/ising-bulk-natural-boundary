import IsingBulk.Analysis.BranchUpper
import IsingBulk.First.RegularPhaseDomain

/-! Compatibility names for the shared whole-upper-half-plane foundations.
No duplicate branch or nonlinear-gap proof is maintained in HT. -/
namespace IsingBulk.HT.First

export IsingBulk.Branch (sqrt_re_nonneg_all inverseCosineRoot_im_pos_of_upper
  inverseCosineRoot_norm_of_upper lowerArccos_sheet_of_upper lowerArccos_analytic_of_upper)
export IsingBulk.First.Regular (lowerArccos_analytic_cos_of_lt_pi
  phaseRoot_norm_lt_one_of_upper phaseRoot_eq_interior_root_of_upper
  exp_pair_denominator_ne_zero_lower_strip nonlinear_exp_gap_signed)

end IsingBulk.HT.First
