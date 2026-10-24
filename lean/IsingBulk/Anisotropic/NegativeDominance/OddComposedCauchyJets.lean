import IsingBulk.Anisotropic.NegativeDominance.OddFullDiskControl
import IsingBulk.Anisotropic.NegativeDominance.AnalyticCoordinateControl

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open IsingBulk.Anisotropic.RegularEdges Set Metric
open scoped Topology

/-- Polynomial-scale full-integrand disk control survives the actual analytic
temperature-coordinate change with constants independent of the particle index. -/
theorem odd_negative_composed_integrand_complex_control {b : ℝ} {B S f : ℂ → ℂ}
    (hb : |b|<1) (hB : 0<(B 0).im) (hBa : AnalyticAt ℂ B 0)
    (hSa : AnalyticAt ℂ S 0) (hS0 : S 0≠0)
    (hf : AnalyticAt ℂ f 0) (hf0 : f 0=0) :
    ∃ a r C M K : ℝ, 0<a ∧ 0<r ∧ r<1 ∧ 0<C ∧ 0<M ∧ 0<K ∧
      ∀ (n : ℕ), Odd (n+1) → ∀ v : Fin n → ℝ, ∀ u : ℂ,
      ‖u‖<a/((n+1 : ℕ) : ℝ)^3 →
        AnalyticAt ℂ (fun w => negativeShiftedFullIntegrand b B S n (f w) v) u ∧
        ‖negativeShiftedFullIntegrand b B S n (f u) v‖≤
          K*((n+1 : ℕ) : ℝ)^2*particleEdgeMajorant r C M (n+1) := by
  obtain ⟨a,r,C,M,K,ha,hr,hr1,hC,hM,hK,hcontrol⟩ :=
    odd_negative_fullIntegrand_complex_control hb hB hBa hSa hS0
  obtain ⟨δ,L,hδ,hL,hlin⟩ := analytic_zero_uniform_linear_bound hf hf0
  refine ⟨min δ (a/L),r,C,M,K,lt_min hδ (div_pos ha hL),hr,hr1,hC,hM,hK,?_⟩
  intro n hn v u hu
  let N : ℝ := (n+1 : ℕ)
  have hN : 1≤N := by dsimp [N]; exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))
  have hN0 : 0<N := lt_of_lt_of_le zero_lt_one hN
  have hN3 : 1≤N^3 := one_le_pow₀ hN
  have hsmall : min δ (a/L)/N^3≤min δ (a/L) :=
    (div_le_iff₀ (pow_pos hN0 _)).mpr (by nlinarith [lt_min hδ (div_pos ha hL)])
  have huδ : ‖u‖<δ := hu.trans_le (hsmall.trans (min_le_left _ _))
  obtain ⟨hfu,hfn⟩ := hlin u huδ
  have hfun : ‖f u‖<a/N^3 := by
    calc
      ‖f u‖ ≤ L*‖u‖ := hfn
      _ < L*(min δ (a/L)/N^3) := mul_lt_mul_of_pos_left hu hL
      _ ≤ L*((a/L)/N^3) := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right (min_le_right _ _) (by positivity)) hL.le
      _ = a/N^3 := by field_simp
  obtain ⟨hA,hbound⟩ := hcontrol n hn v (f u) hfun
  exact ⟨hA.comp hfu,hbound⟩

/-- Cauchy estimates for the actual complete odd integrand, with constants
independent of both derivative order and particle index. -/
theorem odd_negative_composed_integrand_cauchy_jets {b : ℝ} {B S f : ℂ → ℂ}
    (hb : |b|<1) (hB : 0<(B 0).im) (hBa : AnalyticAt ℂ B 0)
    (hSa : AnalyticAt ℂ S 0) (hS0 : S 0≠0)
    (hf : AnalyticAt ℂ f 0) (hf0 : f 0=0) :
    ∃ a r C M K : ℝ, 0<a ∧ 0<r ∧ r<1 ∧ 0<C ∧ 0<M ∧ 0<K ∧
      ∀ (j n : ℕ), Odd (n+1) → ∀ v : Fin n → ℝ, ∀ u : ℂ,
      ‖u‖<a/((n+1 : ℕ) : ℝ)^3 →
        ‖iteratedDeriv j (fun w => negativeShiftedFullIntegrand b B S n (f w) v) u‖≤
          (j.factorial : ℝ)*(K*((n+1 : ℕ) : ℝ)^2*particleEdgeMajorant r C M (n+1))/
            (a/((n+1 : ℕ) : ℝ)^3)^j := by
  obtain ⟨a,r,C,M,K,ha,hr,hr1,hC,hM,hK,hcontrol⟩ :=
    odd_negative_composed_integrand_complex_control hb hB hBa hSa hS0 hf hf0
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
