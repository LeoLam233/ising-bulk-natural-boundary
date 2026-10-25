import IsingBulk.Joint.Negative.FamilyHessianBounds
import IsingBulk.Anisotropic.NegativeCycles.ActualModelTail
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
open Set Metric IsingBulk.Anisotropic.NegativeCycles
namespace IsingBulk.Joint.Negative
open IsingBulk.Anisotropic.NegativeDominance IsingBulk.Anisotropic.NegativeNormalForm IsingBulk.First MeasureTheory Filter
open scoped Topology

/-- The actual Hessian and the fixed cutoff yield a uniform geometric model-tail error.
The threshold is chosen before the derivative order. -/
theorem compact_family_model_cutoff (B : ℂ × E→ℂ) (phi : ℝ) {P : Set E} (hP : IsCompact P) (hB : ∀eta∈P,AnalyticAt ℂ B (0,eta))
    (b : ContDiffBump (0:ℝ)) :
    ∃C : ℝ,0<C ∧ ∀ᶠ N : ℕ in atTop, ∀eta∈P, Odd N → ∀j : ℕ,2*alpha N≤j →
      let h := centralHessian (familyMember B eta) phi ((Real.pi/(N:ℝ):ℝ):ℂ)
      ‖(∫q : Fin (N-1)→ℝ,(shapeSpatialCutoff b q:ℂ)*
        quadraticModelKernel (N-1) j (tau N) (h/(2*(N:ℂ))) q)-
          shapePeriod (N-1) j (tau N) (h/(2*(N:ℂ)))‖≤
        (C*(1/2:ℝ)^j)*‖shapePeriod (N-1) j (tau N) (h/(2*(N:ℂ)))‖ := by
  obtain ⟨r,L,hr,hL,hloss⟩ := compact_family_hessian_period_loss B phi hP hB
  obtain ⟨N₀,hN₀⟩ := exists_nat_ge (32*Real.pi^2/b.rIn)
  have hnear : ∀ᶠ N : ℕ in atTop, ‖((Real.pi/(N:ℝ):ℝ):ℂ)‖<r := by
    simpa only [Metric.mem_ball,dist_zero_right] using
      winding_angle_complex_tendsto_zero.eventually (Metric.ball_mem_nhds (0:ℂ) hr)
  refine ⟨Real.exp (L^2*Real.pi^4),Real.exp_pos _,?_⟩
  filter_upwards [hnear,eventually_ge_atTop N₀,eventually_ge_atTop (3:ℕ)] with N hnear hN₀N hN eta heta ho j hj
  dsimp only
  have hn : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hn1 : (1:ℝ)≤N := by exact_mod_cast (show 1≤N by omega)
  have hlarge : 32*Real.pi^2≤(N:ℝ)*b.rIn :=
    (div_le_iff₀ b.rIn_pos).mp (hN₀.trans (by exact_mod_cast hN₀N))
  obtain ⟨hre,hl⟩ := hloss eta heta N hN ((Real.pi/(N:ℝ):ℝ):ℂ) hnear
  have hang : ‖((Real.pi/(N:ℝ):ℝ):ℂ)‖=Real.pi/(N:ℝ) := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  have hexp : (N:ℝ)^2*‖((Real.pi/(N:ℝ):ℝ):ℂ)‖^4≤Real.pi^4 := by
    rw [hang]
    have he : (N:ℝ)^2*(Real.pi/(N:ℝ))^4=Real.pi^4/(N:ℝ)^2 := by field_simp
    rw [he]
    exact div_le_self (by positivity) (by nlinarith)
  have hnormal : (‖centralHessian (familyMember B eta) phi ((Real.pi/(N:ℝ):ℝ):ℂ)‖/
      (centralHessian (familyMember B eta) phi ((Real.pi/(N:ℝ):ℝ):ℂ)).re)^(alpha N)≤Real.exp (L^2*Real.pi^4) := by
    apply hl.trans
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hexp (sq_nonneg L)]
  have hh := physical_model_cutoff_comparison (n := N-1)
    (by simpa only [Nat.sub_add_cancel (show 1≤N by omega)] using ho) (by omega)
    j (by simpa only [Nat.sub_add_cancel (show 1≤N by omega)] using hj)
    (centralHessian (familyMember B eta) phi ((Real.pi/(N:ℝ):ℝ):ℂ)) hre b
    (by simpa only [Nat.sub_add_cancel (show 1≤N by omega)] using hlarge)
  simp only [Nat.sub_add_cancel (show 1≤N by omega)] at hh
  apply hh.trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hnormal (by positivity : (0:ℝ)≤(1/2)^j)

end IsingBulk.Joint.Negative
