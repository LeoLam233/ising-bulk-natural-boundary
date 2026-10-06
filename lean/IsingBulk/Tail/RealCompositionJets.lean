import IsingBulk.Tail.RealReciprocalJets
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace IsingBulk.Tail
noncomputable section
open Set Filter
open scoped Topology ContDiff
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem real_smooth_composition_jet_bound (f : E → F) (g : F → ℂ) (x : E) (k : ℕ)
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g (f x)) (C D : ℝ)
    (hC : ∀ i ≤ k, ‖iteratedFDeriv ℝ i g (f x)‖ ≤ C)
    (hD : ∀ i, 1 ≤ i → i ≤ k → ‖iteratedFDeriv ℝ i f x‖ ≤ D^i) :
    ‖iteratedFDeriv ℝ k (g ∘ f) x‖ ≤ k.factorial*C*D^k := by
  have he := (hg.of_le (show (k:ℕ∞ω) ≤ ∞ by simp)).eventually (by simp)
  obtain ⟨V,hV,hVo,hfx⟩ := eventually_nhds_iff.mp he
  have hfnear := (hf.of_le (show (k:ℕ∞ω) ≤ ∞ by simp)).eventually (by simp)
  have hpre := hf.continuousAt.preimage_mem_nhds (hVo.mem_nhds hfx)
  obtain ⟨U,hU,hUo,hx⟩ := eventually_nhds_iff.mp (hfnear.and hpre)
  have hh := norm_iteratedFDerivWithin_comp_le
    (fun y hy => (hV y hy).contDiffWithinAt)
    (fun y hy => (hU y hy).1.contDiffWithinAt) (n := k) (by simp)
    hVo.uniqueDiffOn hUo.uniqueDiffOn (fun y hy => (hU y hy).2) hx
    (C := C) (D := D)
    (by simpa only [iteratedFDerivWithin_of_isOpen _ hVo hfx] using hC)
    (by simpa only [iteratedFDerivWithin_of_isOpen _ hUo hx] using hD)
  simpa only [iteratedFDerivWithin_of_isOpen _ hUo hx] using hh

theorem real_cexp_jet_norm (z : ℂ) (k : ℕ) :
    ‖iteratedFDeriv ℝ k Complex.exp z‖=‖Complex.exp z‖ := by
  have hc : ContDiffAt ℂ (k:ℕ∞ω) Complex.exp z := Complex.contDiff_exp.contDiffAt
  rw [← hc.restrictScalars_iteratedFDeriv (𝕜 := ℝ)]
  simp only [Function.comp_apply,ContinuousMultilinearMap.norm_restrictScalars,
    norm_iteratedFDeriv_eq_norm_iteratedDeriv,iteratedDeriv_eq_iterate,Complex.iter_deriv_exp]

theorem real_cexp_uniform_jets (f : E → ℂ) (x : E) (J : ℕ) (A B : ℝ)
    (hf : ContDiffAt ℝ ∞ f x) (hA : 0 ≤ A) (hB : 1 ≤ B) (he : ‖Complex.exp (f x)‖ ≤ A)
    (hb : ∀ k, 1 ≤ k → k ≤ J → ‖iteratedFDeriv ℝ k f x‖ ≤ B) :
    ∀ k ≤ J, ‖iteratedFDeriv ℝ k (fun y => Complex.exp (f y)) x‖ ≤ (J.factorial:ℝ)*A*B^J := by
  intro k hk
  have hh := smooth_composition_jet_bound f Complex.exp x k hf Complex.contDiff_exp.contDiffAt A B
    (fun i _ => by simpa only [real_cexp_jet_norm] using he)
    (fun i hi hik => (hb i hi (hik.trans hk)).trans (le_self_pow₀ hB (by omega : i ≠ 0)))
  exact hh.trans (by gcongr)

end
end IsingBulk.Tail
