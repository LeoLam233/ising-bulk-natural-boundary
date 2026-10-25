import IsingBulk.Joint.Negative.FamilyHessianBounds
import IsingBulk.Anisotropic.NegativeNormalForm.CentralPeriodUniformLoss

namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter Metric IsingBulk.Anisotropic.NegativeNormalForm
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
open IsingBulk.Anisotropic.NegativeDominance
open scoped Topology
theorem compact_family_central_period_loss (B : ℂ × E→ℂ) (phi : ℝ)
    {P : Set E} (hP : IsCompact P) (hB : ∀eta∈P,AnalyticAt ℂ B (0,eta)) :
    ∃F : ℝ,0<F ∧ ∀ᶠ N : ℕ in atTop, ∀eta∈P,
      let H := centralHessian (familyMember B eta) phi ((Real.pi/(N:ℝ):ℝ):ℂ)
      let c := H/((2*(N:ℝ):ℝ):ℂ)
      (1:ℝ)/2≤H.re ∧ (‖c‖/c.re)^alpha N≤F := by
  obtain ⟨r,L,hr,_hL,hbound⟩ := compact_family_hessian_period_loss B phi hP hB
  have hnear : ∀ᶠ N : ℕ in atTop, ‖((Real.pi/(N:ℝ):ℝ):ℂ)‖<r := by
    have hh := winding_angle_complex_tendsto_zero (Metric.ball_mem_nhds (0:ℂ) hr)
    change ∀ᶠ N : ℕ in atTop, ((Real.pi/(N:ℝ):ℝ):ℂ)∈Metric.ball 0 r at hh
    simpa only [Metric.mem_ball,dist_zero_right] using hh
  refine ⟨Real.exp (L^2*Real.pi^4),Real.exp_pos _,?_⟩
  filter_upwards [hnear,eventually_ge_atTop (3:ℕ)] with N hnear hN eta heta
  dsimp only
  have hn : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hn1 : (1:ℝ)≤N := by exact_mod_cast (show 1≤N by omega)
  obtain ⟨hre,hl⟩ := hbound eta heta N hN ((Real.pi/(N:ℝ):ℝ):ℂ) hnear
  refine ⟨hre,?_⟩
  rw [curvature_norm_ratio _ _ (by positivity) (by linarith)]
  apply hl.trans
  apply Real.exp_le_exp.mpr
  have hang : ‖((Real.pi/(N:ℝ):ℝ):ℂ)‖=Real.pi/(N:ℝ) := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  have hexp : (N:ℝ)^2*‖((Real.pi/(N:ℝ):ℝ):ℂ)‖^4≤Real.pi^4 := by
    rw [hang]
    have he : (N:ℝ)^2*(Real.pi/(N:ℝ))^4=Real.pi^4/(N:ℝ)^2 := by field_simp
    rw [he]
    exact div_le_self (by positivity) (by nlinarith)
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hexp (sq_nonneg L)

end
end IsingBulk.Joint.Negative
