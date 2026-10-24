import IsingBulk.Anisotropic.NegativeCycles.ActualModelTail

noncomputable section
namespace IsingBulk.Anisotropic.NegativeCycles
open IsingBulk.Anisotropic.NegativeDominance IsingBulk.Anisotropic.NegativeNormalForm IsingBulk.First MeasureTheory Filter
open scoped Topology

/-- Both central winding sectors, with their actual common center amplitude,
may be completed to the whole model period with a uniform 2^-j error. -/
theorem actual_model_cutoff_normalized (B rootB : ℂ→ℂ) (phi : ℝ)
    (hB : AnalyticAt ℂ B 0) (b : ContDiffBump (0:ℝ)) :
    ∃C : ℝ,0<C ∧ ∀ᶠ N : ℕ in atTop, Odd N → ∀j : ℕ,2*alpha N≤j →
      let h := centralHessian B phi ((Real.pi/(N:ℝ):ℝ):ℂ)
      let A := 2*centralDensity (B (tau N)) (rootB (tau N)) (Real.sin phi) N
      let M := model (B (tau N)) (rootB (tau N)) h (Real.sin phi) N j
      ‖A*(∫q : Fin (N-1)→ℝ,(shapeSpatialCutoff b q:ℂ)*
        quadraticModelKernel (N-1) j (tau N) (h/(2*(N:ℂ))) q)-M‖≤
          (C*(1/2:ℝ)^j)*‖M‖ := by
  obtain ⟨C,hC,hcut⟩ := actual_model_cutoff_eventually B phi hB b
  obtain ⟨r,hr,hre⟩ := centralHessian_uniform_rightHalfPlane B phi hB
  have hnear : ∀ᶠ N : ℕ in atTop, ‖((Real.pi/(N:ℝ):ℝ):ℂ)‖<r := by
    simpa only [Metric.mem_ball,dist_zero_right] using
      winding_angle_complex_tendsto_zero.eventually (Metric.ball_mem_nhds (0:ℂ) hr)
  refine ⟨C,hC,?_⟩
  filter_upwards [hcut,hnear,eventually_ge_atTop (3:ℕ)] with N hc hn hN ho j hj
  dsimp only
  rw [←centralDensity_complex_period_eq_model ho hN (B (tau N)) (rootB (tau N))
    (centralHessian B phi ((Real.pi/(N:ℝ):ℝ):ℂ)) (Real.sin phi) (hre _ hn) j (by omega)]
  rw [←mul_sub]
  have hb := mul_le_mul_of_nonneg_left (hc ho j hj)
    (norm_nonneg (2*centralDensity (B (tau N)) (rootB (tau N)) (Real.sin phi) N))
  simp only [norm_mul] at hb ⊢
  simpa only [mul_assoc,mul_left_comm,mul_comm] using hb

end IsingBulk.Anisotropic.NegativeCycles
