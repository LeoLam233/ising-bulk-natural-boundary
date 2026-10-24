import IsingBulk.Anisotropic.NegativeDominance.OddFullDiskControl

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open IsingBulk.Anisotropic.RegularEdges Set Metric
open scoped Topology

/-- Cauchy estimates for the actual complete odd integrand, with constants
independent of both derivative order and particle index. -/
theorem odd_negative_fullIntegrand_cauchy_jets {b : ℝ} {B S : ℂ → ℂ}
    (hb : |b|<1) (hB : 0<(B 0).im) (hBa : AnalyticAt ℂ B 0)
    (hSa : AnalyticAt ℂ S 0) (hS0 : S 0≠0) :
    ∃ a r C M K : ℝ, 0<a ∧ 0<r ∧ r<1 ∧ 0<C ∧ 0<M ∧ 0<K ∧
      ∀ (j n : ℕ), Odd (n+1) → ∀ v : Fin n → ℝ, ∀ u : ℂ,
      ‖u‖<a/((n+1 : ℕ) : ℝ)^3 →
        ‖iteratedDeriv j (fun w => negativeShiftedFullIntegrand b B S n w v) u‖≤
          (j.factorial : ℝ)*(K*((n+1 : ℕ) : ℝ)^2*particleEdgeMajorant r C M (n+1))/
            (a/((n+1 : ℕ) : ℝ)^3)^j := by
  obtain ⟨a,r,C,M,K,ha,hr,hr1,hC,hM,hK,hcontrol⟩ :=
    odd_negative_fullIntegrand_complex_control hb hB hBa hSa hS0
  refine ⟨a/3,r,C,M,K,by positivity,hr,hr1,hC,hM,hK,?_⟩
  intro j n hn v u hu
  let R : ℝ := (a/3)/((n+1 : ℕ) : ℝ)^3
  have hR : 0<R := by dsimp [R]; positivity
  have hbig : a/((n+1 : ℕ) : ℝ)^3=3*R := by dsimp [R]; ring
  have hsub : closedBall u R ⊆ ball 0 (a/((n+1 : ℕ) : ℝ)^3) := by
    intro w hw
    have hwu : ‖w-u‖≤R := by simpa only [mem_closedBall,dist_eq_norm] using hw
    have htri := norm_add_le (w-u) u
    rw [sub_add_cancel] at htri
    change dist w 0<a/((n+1 : ℕ) : ℝ)^3
    rw [dist_zero_right,hbig]
    change ‖u‖<R at hu
    linarith
  apply Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le j hR
  · apply DifferentiableOn.diffContOnCl_ball
      (U := ball 0 (a/((n+1 : ℕ) : ℝ)^3)) _ hsub
    intro w hw
    exact (hcontrol n hn v w (by simpa only [mem_ball,dist_zero_right] using hw)).1.differentiableAt.differentiableWithinAt
  · intro w hw
    exact (hcontrol n hn v w
      (by simpa only [mem_ball,dist_zero_right] using hsub (sphere_subset_closedBall hw))).2

end
end IsingBulk.Anisotropic.NegativeDominance
