import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Tactic

/-! Connected complex exterior domains and holomorphic symmetry transforms.
Existence of a named exterior continuation is kept separate from any source series. -/
namespace IsingBulk.First
noncomputable section
open Complex Set Filter Metric
open scoped Topology

def complexNormExterior (R : ℝ) : Set ℂ := {s | R < ‖s‖}

theorem complexNormExterior_isOpen (R : ℝ) : IsOpen (complexNormExterior R) :=
  isOpen_lt continuous_const continuous_norm

theorem complexNormExterior_isPreconnected {R : ℝ} (hR : 0 ≤ R) :
    IsPreconnected (complexNormExterior R) := by
  have hs : IsPreconnected (sphere (0:ℂ) 1) :=
    isPreconnected_sphere (by simp [Complex.rank_real_complex]) (0:ℂ) 1
  have hp : IsPreconnected (Ioi R ×ˢ sphere (0:ℂ) 1) := isPreconnected_Ioi.prod hs
  let f : ℝ × ℂ → ℂ := fun q => q.1 • q.2
  have hf : Continuous f := continuous_fst.smul continuous_snd
  have he : f '' (Ioi R ×ˢ sphere (0:ℂ) 1) = complexNormExterior R := by
    ext z
    constructor
    · rintro ⟨⟨r,u⟩,⟨hr,hu⟩,rfl⟩
      have hrp : 0 < r := hR.trans_lt hr
      have hun : ‖u‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using hu
      change R < ‖r • u‖
      rwa [norm_smul,Real.norm_eq_abs,abs_of_pos hrp,hun,mul_one]
    · intro hz
      have hzp : 0 < ‖z‖ := hR.trans_lt hz
      refine ⟨(‖z‖,‖z‖⁻¹ • z),⟨hz,?_⟩,?_⟩
      · simp only [mem_sphere,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_inv,
          abs_norm,inv_mul_cancel₀ hzp.ne']
      · change (‖z‖:ℂ)*(((‖z‖⁻¹:ℝ):ℂ)*z)=z
        rw [← mul_assoc,← Complex.ofReal_mul,mul_inv_cancel₀ hzp.ne',Complex.ofReal_one,one_mul]
  rw [← he]
  exact hp.image f hf.continuousOn

theorem analyticOnNhd_exterior_neg {R : ℝ} {chi : ℂ → ℂ}
    (hchi : AnalyticOnNhd ℂ chi (complexNormExterior R)) :
    AnalyticOnNhd ℂ (fun s => chi (-s)) (complexNormExterior R) := by
  intro s hs
  have hn : -s ∈ complexNormExterior R := by simpa only [complexNormExterior,mem_ofPred_eq,norm_neg] using hs
  exact (hchi (-s) hn).comp (f := fun s : ℂ => -s) analyticAt_id.neg

/-- Conjugating both argument and value is holomorphic; neither conjugation
alone is treated as a complex-linear map. -/
theorem analyticOnNhd_exterior_conjugate_reflection {R : ℝ} {chi : ℂ → ℂ}
    (hchi : AnalyticOnNhd ℂ chi (complexNormExterior R)) :
    AnalyticOnNhd ℂ (fun s => star (chi (star s))) (complexNormExterior R) := by
  intro s hs
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  filter_upwards [(complexNormExterior_isOpen R).mem_nhds hs] with z hz
  have hzc : star z ∈ complexNormExterior R := by
    simpa only [complexNormExterior,mem_ofPred_eq,norm_star] using hz
  simpa only [Function.comp_def,star_star] using (hchi (star z) hzc).differentiableAt.star_star

end
end IsingBulk.First
