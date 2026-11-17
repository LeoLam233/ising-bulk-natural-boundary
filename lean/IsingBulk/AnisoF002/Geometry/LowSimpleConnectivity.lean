import IsingBulk.AnisoF002.Geometry.LowComponent
import Mathlib.Analysis.Convex.Contractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# Simple connectivity of the full physical LT epigraph

This is F002 `thm:components`' explicit shear homeomorphism
`(x,y) ↦ (x-L(y),y)`.  The graph function is the actual profile already
constructed in `ProfileBounds`, and its continuity is a proved theorem.
-/

namespace IsingBulk.AnisoF002.Geometry
noncomputable section

def lowShearF002 {lam : ℝ} (hlam : 0 < lam) : ℂ ≃ₜ ℂ where
  toFun z := z - (lowProfileF002 lam z.im : ℂ)
  invFun z := z + (lowProfileF002 lam z.im : ℂ)
  left_inv z := by simp
  right_inv z := by simp
  continuous_toFun := continuous_id.sub
    (Complex.continuous_ofReal.comp ((lowProfile_continuous hlam).comp Complex.continuous_im))
  continuous_invFun := continuous_id.add
    (Complex.continuous_ofReal.comp ((lowProfile_continuous hlam).comp Complex.continuous_im))

theorem omegaLF002_eq_shear_preimage {lam : ℝ} (hlam : 0 < lam) :
    omegaLF002 lam = (lowShearF002 hlam) ⁻¹' {z : ℂ | 0 < z.re} := by
  ext z
  change lowProfileF002 lam z.im < z.re ↔ 0 < (z - (lowProfileF002 lam z.im : ℂ)).re
  simp only [Complex.sub_re, Complex.ofReal_re, sub_pos]

theorem omegaLF002_isSimplyConnected {lam : ℝ} (hlam : 0 < lam) :
    IsSimplyConnected (omegaLF002 lam) := by
  rw [omegaLF002_eq_shear_preimage hlam, Homeomorph.isSimplyConnected_preimage]
  have hc : Convex ℝ {z : ℂ | 0 < z.re} :=
    (convex_Ioi (0 : ℝ)).linear_preimage Complex.reCLM.toLinearMap
  change SimplyConnectedSpace _
  exact @SimplyConnectedSpace.ofContractible _ _ (hc.contractibleSpace ⟨1, by norm_num⟩)

end
end IsingBulk.AnisoF002.Geometry
