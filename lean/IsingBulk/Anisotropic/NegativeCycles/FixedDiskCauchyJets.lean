import IsingBulk.Anisotropic.NegativeCycles.UniformDividedDifference
import Mathlib.Analysis.Complex.Liouville

namespace IsingBulk.Anisotropic.NegativeCycles
noncomputable section
open Set Metric

theorem analytic_disk_iterated_deriv_bound {f : ℂ → ℂ} {r M : ℝ} (hr : 0<r)
    (hf : AnalyticOnNhd ℂ f (ball 0 r)) (hb : ∀ z∈ball 0 r, ‖f z‖≤M) (j : ℕ) :
    ‖iteratedDeriv j f 0‖≤(j.factorial:ℝ)*M/(r/2)^j := by
  have hsub : closedBall (0:ℂ) (r/2)⊆ball 0 r := by
    intro z hz
    have hh : ‖z‖≤r/2 := by simpa using hz
    simpa only [mem_ball,dist_zero_right] using (show ‖z‖<r by linarith)
  apply Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le j (by positivity : 0<r/2)
  · apply DifferentiableOn.diffContOnCl_ball (U := ball (0:ℂ) r) _ hsub
    exact hf.differentiableOn
  · intro z hz
    exact hb z (hsub (sphere_subset_closedBall hz))

theorem analytic_disk_normalized_jet_bound {f : ℂ → ℂ} {r M : ℝ} (hr : 0<r)
    (hf : AnalyticOnNhd ℂ f (ball 0 r)) (hb : ∀ z∈ball 0 r, ‖f z‖≤M) (j : ℕ) :
    ‖iteratedDeriv j f 0/(j.factorial:ℂ)‖≤M/(r/2)^j := by
  rw [norm_div,Complex.norm_natCast]
  have h := div_le_div_of_nonneg_right (analytic_disk_iterated_deriv_bound hr hf hb j)
    (Nat.cast_nonneg j.factorial : (0:ℝ)≤j.factorial)
  have hn : (j.factorial:ℝ)≠0 := by exact_mod_cast Nat.factorial_ne_zero j
  convert h using 1
  field_simp

end
end IsingBulk.Anisotropic.NegativeCycles
