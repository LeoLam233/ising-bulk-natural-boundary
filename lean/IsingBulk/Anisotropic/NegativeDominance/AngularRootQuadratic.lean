import IsingBulk.Anisotropic.NegativeDominance.UniformRootLipschitz
import IsingBulk.Anisotropic.NegativeDominance.OddBoundaryGap

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open IsingBulk.Tail IsingBulk.Anisotropic.RegularEdges Set
open scoped BigOperators

/-- Actual angular roots differ quadratically from their common central value,
with one constant before the dimension. -/
theorem edgeRoot_angular_quadratic {b : ℝ} {B : ℂ} (hb : |b|<1) (hB : 0<B.im) :
    ∃K : ℝ,0<K ∧ ∀q : ℝ,‖edgeRoot b B q-continuedRoot (b : ℂ)‖≤K*q^2 := by
  obtain ⟨δ,L,hδ,hL,hroot⟩ := edgeParamRoot_uniform_lipschitz_zero (B := fun _=>B) hb hB analyticAt_const
  let σ := δ/(‖B‖+1)
  have hσ : 0<σ := by dsimp [σ]; positivity
  have hσeq : (‖B‖+1)*σ=δ := by dsimp [σ]; field_simp
  refine ⟨L*‖B‖+2/σ,by positivity,?_⟩
  intro q
  have hbase : ‖continuedRoot (b : ℂ)‖≤1 := by
    simpa [edgeRoot,edgeW] using (edgeRoot_bounds hb hB 0).1
  by_cases hq : q^2≤σ
  · let u : ℂ := B*((1-Real.cos q : ℝ) : ℂ)
    have huNorm : ‖u‖=‖B‖*(1-Real.cos q) := by
      dsimp [u]
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr (Real.cos_le_one q))]
    have hcos : 1-Real.cos q≤q^2/2 := by linarith [Real.one_sub_sq_div_two_le_cos (x := q)]
    have hu : ‖u‖<δ := by
      rw [huNorm]
      have hh := mul_le_mul_of_nonneg_left hcos (norm_nonneg B)
      have hh' := mul_le_mul_of_nonneg_left hq (norm_nonneg B)
      nlinarith [norm_nonneg B]
    have hh := (hroot u hu 0 ⟨by linarith [Real.pi_pos],by linarith [Real.pi_pos]⟩).2
    have he : edgeParamRoot b (fun _=>B) u 0=edgeRoot b B q := by
      simp [edgeParamRoot,edgeParamW,edgeRoot,edgeW,u]
    have he0 : edgeParamRoot b (fun _=>B) 0 0=continuedRoot (b : ℂ) := by
      simp [edgeParamRoot,edgeParamW]
    rw [he,he0,huNorm] at hh
    have hmul := mul_le_mul_of_nonneg_left hcos (mul_nonneg hL.le (norm_nonneg B))
    have hextra : 0≤(2/σ)*q^2 := by positivity
    have hbase' : 0≤L*‖B‖*q^2 := by positivity
    nlinarith
  · have hq' : σ≤q^2 := le_of_not_ge hq
    have hqgap : 2≤(2/σ)*q^2 := by
      have hh := mul_le_mul_of_nonneg_left hq' (show 0≤2/σ by positivity)
      have he : (2/σ)*σ=2 := by field_simp
      rwa [he] at hh
    have hdiff := norm_sub_le (edgeRoot b B q) (continuedRoot (b : ℂ))
    have hnonneg : 0≤L*‖B‖*q^2 := by positivity
    nlinarith [(edgeRoot_bounds hb hB q).1]

end
end IsingBulk.Anisotropic.NegativeDominance
