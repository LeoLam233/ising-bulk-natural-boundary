import IsingBulk.Tail.RealScaledJetBounds

namespace IsingBulk.Tail
noncomputable section
open Set Filter
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem parameterSmooth_angular_uniform_jets {Ω : Set (ℂ × E)} (hΩ : IsOpen Ω)
    {F : ℂ → E → ℂ} (hF : ParameterSmoothOn Ω F) {p : ℂ × E} (hp : p ∈ Ω)
    (J : ℕ) (C : ℝ) (hC : 0 ≤ C) (v : E) (hv : ‖v‖ ≤ 1)
    (hb : ∀ k, 1 ≤ k → k ≤ J+1 → ‖iteratedFDeriv ℝ k (Function.uncurry F) p‖ ≤ C) :
    RealScaledJetBound (fun q : ℂ × E => fderiv ℝ (F q.1) q.2 v) p J 1 C 0 := by
  have hh := real_direction_uniform_jets (hF p hp).1 hC (0,v)
    (by simpa only [Prod.norm_def,norm_zero,max_le_iff] using And.intro zero_le_one hv) hb
  apply hh.congr
  filter_upwards [hΩ.mem_nhds hp] with q hq
  exact angularSlice_fderiv (Function.uncurry F) q ((hF q hq).1.differentiableAt (by simp)) v

theorem parameterSmooth_parameter_uniform_jets {Ω : Set (ℂ × E)} (hΩ : IsOpen Ω)
    {F : ℂ → E → ℂ} (hF : ParameterSmoothOn Ω F) {p : ℂ × E} (hp : p ∈ Ω)
    (J : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ k, 1 ≤ k → k ≤ J+1 → ‖iteratedFDeriv ℝ k (Function.uncurry F) p‖ ≤ C) :
    RealScaledJetBound (fun q : ℂ × E => deriv (fun s => F s q.2) q.1) p J 1 C 0 := by
  have hh := real_direction_uniform_jets (hF p hp).1 hC (1,0)
    (by simp [Prod.norm_def]) hb
  apply hh.congr
  filter_upwards [hΩ.mem_nhds hp] with q hq
  have hCR := differentiableAt_complex_iff_differentiableAt_real.mp (hF q hq).2
  rw [complexOfReal_deriv hCR.1 hCR.2]
  exact parameterSlice_fderiv (Function.uncurry F) q ((hF q hq).1.differentiableAt (by simp)) 1

end
end IsingBulk.Tail
