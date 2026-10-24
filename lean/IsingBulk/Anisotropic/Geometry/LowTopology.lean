import IsingBulk.Anisotropic.Geometry.Profiles
import Mathlib.Analysis.Convex.Contractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

namespace IsingBulk.Anisotropic
noncomputable section

/-- Straighten the entire continuous graph without imposing periodicity. -/
def lowStraightening (lam : ℝ) (hlam : 0 < lam) : ℂ ≃ₜ ℂ where
  toFun z := z - (sliceL lam z.im : ℂ)
  invFun z := z + (sliceL lam z.im : ℂ)
  left_inv z := by simp
  right_inv z := by simp
  continuous_toFun := continuous_id.sub
    (Complex.continuous_ofReal.comp ((sliceL_continuous hlam).comp Complex.continuous_im))
  continuous_invFun := continuous_id.add
    (Complex.continuous_ofReal.comp ((sliceL_continuous hlam).comp Complex.continuous_im))

theorem omegaL_eq_halfPlane_preimage {lam : ℝ} (hlam : 0 < lam) :
    omegaL lam = lowStraightening lam hlam ⁻¹' {z : ℂ | 0 < z.re} := by
  ext z
  change sliceL lam z.im < z.re ↔ 0 < (z - (sliceL lam z.im : ℂ)).re
  simp only [Complex.sub_re, Complex.ofReal_re, sub_pos]

/-- Simple connectivity of the full, unbounded physical LT epigraph. -/
theorem omegaL_isSimplyConnected {lam : ℝ} (hlam : 0 < lam) :
    IsSimplyConnected (omegaL lam) := by
  rw [omegaL_eq_halfPlane_preimage hlam, Homeomorph.isSimplyConnected_preimage]
  have hc : Convex ℝ {z : ℂ | 0 < z.re} := by
    intro x hx y hy a b ha hb hab
    change 0 < (a • x + b • y).re
    simp only [Complex.add_re, Complex.smul_re, smul_eq_mul]
    change 0 < x.re at hx
    change 0 < y.re at hy
    by_cases ha0 : a = 0
    · simp only [ha0, zero_add] at hab
      simpa only [ha0, hab, zero_mul, one_mul, zero_add] using hy
    · exact add_pos_of_pos_of_nonneg (mul_pos (lt_of_le_of_ne ha (Ne.symm ha0)) hx)
        (mul_nonneg hb hy.le)
  have hn : ({z : ℂ | 0 < z.re} : Set ℂ).Nonempty := ⟨1, by norm_num⟩
  let : ContractibleSpace ({z : ℂ | 0 < z.re} : Set ℂ) := hc.contractibleSpace hn
  change SimplyConnectedSpace _
  infer_instance

end
end IsingBulk.Anisotropic
