import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic

namespace IsingBulk.Anisotropic.Algebra
noncomputable section
open scoped BigOperators

/-- Uniform-weight AM-GM in an integer-power form suitable for Gram spectra. -/
theorem prod_le_arithmetic_mean_pow {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hcard : 0 < Fintype.card ι) :
    (∏ i, a i) ≤ ((∑ i, a i) / Fintype.card ι) ^ Fintype.card ι := by
  classical
  have hn : (0:ℝ) < Fintype.card ι := by exact_mod_cast hcard
  have hp : 0 ≤ ∏ i, a i := Finset.prod_nonneg fun i _ => ha i
  have hs : 0 ≤ (∑ i, a i) / Fintype.card ι :=
    div_nonneg (Finset.sum_nonneg fun i _ => ha i) hn.le
  have h := Real.geom_mean_le_arith_mean Finset.univ (fun _ : ι => (1:ℝ)) a
    (fun _ _ => zero_le_one) (by simpa using hn) (fun i _ => ha i)
  simp only [Real.rpow_one,one_mul,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at h
  have hh := pow_le_pow_left₀ (Real.rpow_nonneg hp _) h (Fintype.card ι)
  have hid : ((∏ i, a i) ^ ((Fintype.card ι:ℝ)⁻¹)) ^ Fintype.card ι = ∏ i, a i := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hp,inv_mul_cancel₀ hn.ne',Real.rpow_one]
  rwa [hid] at hh

end
end IsingBulk.Anisotropic.Algebra
