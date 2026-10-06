import IsingBulk.Analysis.BranchTheorem

/-! Projections of the constructed branch conclusion on its common closed arc.
The occupancy specialization keeps P fixed during every real-u derivative. -/
namespace IsingBulk.Branch
noncomputable section
open MeasureTheory Set

theorem reciprocal_sqrt_rpow (u : ℝ) (hu : 0 < u) :
    1/Real.sqrt u = u^(-(1/2:ℝ)) := by
  rw [Real.rpow_neg hu.le, ← Real.sqrt_eq_rpow, one_div]

theorem reciprocal_three_halves_rpow (u : ℝ) (hu : 0 < u) :
    1/(u*Real.sqrt u) = u^(-(3/2:ℝ)) := by
  rw [Real.rpow_neg hu.le]
  have hp : u^(3/2:ℝ) = u*Real.sqrt u := by
    rw [show (3/2:ℝ) = 1+1/2 by norm_num, Real.rpow_add hu,
      Real.rpow_one, ← Real.sqrt_eq_rpow]
  rw [hp, one_div]

theorem BranchEstimates.positive_slope {d : LocalBranchData} (B : BranchEstimates d)
    (ε u : ℝ) (hε : 0 < ε) (hε₀ : ε ≤ B.ε₀) (hu : 0 ≤ u) (hur : u ≤ B.r) :
    0 < deriv (originalRealPhase d ε) u ∧
    B.original.a/Real.sqrt (u+ε) ≤ deriv (originalRealPhase d ε) u ∧
    deriv (originalRealPhase d ε) u ≤ B.original.C/Real.sqrt (u+ε) := by
  have h := B.original.slope ε u hε ((hε₀.trans B.ε₀_le_r).trans_lt B.original_radius)
    hu (hur.trans_lt B.original_radius)
  exact ⟨(div_pos B.original.a_pos (Real.sqrt_pos.mpr (by linarith))).trans_le h.1,h⟩

theorem BranchEstimates.concavity {d : LocalBranchData} (B : BranchEstimates d)
    (ε u : ℝ) (hε : 0 < ε) (hε₀ : ε ≤ B.ε₀)
    (hscale : B.original.C₀*ε ≤ u) (hur : u ≤ B.r) :
    B.original.k*u^(-(3/2:ℝ)) ≤ -deriv (deriv (originalRealPhase d ε)) u := by
  have hu : 0 < u := (mul_pos B.original.C₀_pos hε).trans_le hscale
  rw [← reciprocal_three_halves_rpow u hu, mul_one_div]
  exact B.original.concavity ε u hε ((hε₀.trans B.ε₀_le_r).trans_lt B.original_radius)
    hscale (hur.trans_lt B.original_radius)

theorem BranchEstimates.separated {d : LocalBranchData} (B : BranchEstimates d)
    (ε m M : ℝ) (hε : 0 < ε) (hε₀ : ε ≤ B.ε₀)
    (hm : 0 ≤ m) (hmM : m ≤ M/2) (hMr : M ≤ B.r)
    (hsep : B.original.separationThreshold*ε ≤ M) :
    min (B.original.k/4) (B.original.a/2)/Real.sqrt (m+ε) ≤
      deriv (originalRealPhase d ε) m-deriv (originalRealPhase d ε) M ∧
    0 < deriv (originalRealPhase d ε) m-deriv (originalRealPhase d ε) M ∧
    ‖deriv (originalPhase d ε) m*deriv (originalPhase d ε) M‖ /
      (deriv (originalRealPhase d ε) m-deriv (originalRealPhase d ε) M) ≤
      (B.original.C^2/min (B.original.k/4) (B.original.a/2))/Real.sqrt M := by
  have he := (hε₀.trans B.ε₀_le_r).trans_lt B.original_radius
  have hM := hMr.trans_lt B.original_radius
  exact ⟨B.original.separated_difference ε m M hε he hm hmM hM hsep,
    B.original.separated_quotient ε m M hε he hm hmM hM hsep⟩

theorem BranchEstimates.comparable {d : LocalBranchData} (B : BranchEstimates d)
    (ε m M : ℝ) (hε : 0 < ε) (hε₀ : ε ≤ B.ε₀)
    (hscale : B.original.C₀*ε ≤ m) (hm : M/2 < m) (hmM : m < M) (hMr : M ≤ B.r) :
    0 < deriv (originalRealPhase d ε) m-deriv (originalRealPhase d ε) M ∧
    ‖deriv (originalPhase d ε) m*deriv (originalPhase d ε) M‖ /
      (deriv (originalRealPhase d ε) m-deriv (originalRealPhase d ε) M) ≤
      (2*B.original.C^2/B.original.k)*Real.sqrt M/(M-m) :=
  B.original.comparable_quotient ε m M hε
    ((hε₀.trans B.ε₀_le_r).trans_lt B.original_radius) hscale hm hmM
    (hMr.trans_lt B.original_radius)

theorem BranchEstimates.original_sheet {d : LocalBranchData} (B : BranchEstimates d)
    (ε u : ℝ) (hε : 0 < ε) (hε₀ : ε ≤ B.ε₀) (hur : |u| ≤ B.r) :
    Complex.cos (originalPhase d ε u) = originalW d ε u ∧
    0 < (originalPhase d ε u).re ∧ (originalPhase d ε u).re < Real.pi/2 ∧
    (originalPhase d ε u).im < 0 := by
  obtain ⟨hre,him⟩ := B.quadrant ε u hε hε₀ hur
  exact lowerArccos_sheet _ hre him

theorem BranchEstimates.current_sheet {d : LocalBranchData} (B : BranchEstimates d)
    (ε lam ρ u : ℝ) (h : CurrentParameters d B.ε₀ ε lam ρ) (hur : |u| ≤ B.r) :
    Complex.cos (currentPhase d ε (lam*ρ) u) = currentW d ε (lam*ρ) u ∧
    0 < (currentPhase d ε (lam*ρ) u).re ∧
    (currentPhase d ε (lam*ρ) u).re < Real.pi/2 ∧
    (currentPhase d ε (lam*ρ) u).im < 0 := by
  obtain ⟨hre,him⟩ := (B.current ε lam ρ u h hur).1
  exact lowerArccos_sheet _ hre him

theorem BranchEstimates.current_occupancy {d : LocalBranchData} (B : BranchEstimates d)
    (ε lam P u : ℝ) (N : ℕ) (hε : 0 < ε) (hε₀ : ε ≤ B.ε₀)
    (hlam : 0 ≤ lam) (hlampow : lam ≤ ε^d.alpha)
    (hN : 0 < N) (hP : 0 ≤ P) (hPN : P ≤ N) (hur : |u| ≤ 2*(B.r/2)) :
    (0 ≤ lam*(P/N) ∧ lam*(P/N) < B.r) ∧
    (0 < (currentW d ε (lam*(P/N)) u).re ∧ 0 < (currentW d ε (lam*(P/N)) u).im) ∧
    (B.magnitudeLower/Real.sqrt (|u|+ε+lam*(P/N)) ≤ ‖deriv (currentPhase d ε (lam*(P/N))) u‖ ∧
      ‖deriv (currentPhase d ε (lam*(P/N))) u‖ ≤ B.magnitudeUpper/Real.sqrt (|u|+ε+lam*(P/N))) ∧
    (u ≤ 0 → B.attenuationLower*Real.sqrt (|u|+ε+lam*(P/N)) ≤ -(currentPhase d ε (lam*(P/N)) u).im) ∧
    (0 ≤ u → (2/3:ℝ)*‖deriv (currentPhase d ε (lam*(P/N))) u‖ ≤
      (deriv (currentPhase d ε (lam*(P/N))) u).re) := by
  have hn : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have h : CurrentParameters d B.ε₀ ε lam (P/N) :=
    ⟨hε,hε₀,hlam,hlampow,div_nonneg hP hn.le,(div_le_one hn).mpr hPN⟩
  exact ⟨B.current_range ε lam (P/N) h,B.current ε lam (P/N) u h (by linarith)⟩

/-- The source chooses r0=deltaB/(2*L^2). Its inner support lies in the
proved common arc when the outer branch support does and L>=1. -/
theorem BranchEstimates.source_inner_radius {d : LocalBranchData} (B : BranchEstimates d)
    (deltaB L u : ℝ) (hdelta : 0 ≤ deltaB) (hdeltar : deltaB ≤ B.r)
    (hL : 1 ≤ L) (hu : |u| ≤ 2*(deltaB/(2*L^2))) :
    |u| ≤ 2*(B.r/2) := by
  have hLpos : 0 < L := by linarith
  have hLsq : 1 ≤ L^2 := by nlinarith
  calc
    |u| ≤ 2*(deltaB/(2*L^2)) := hu
    _ = deltaB/L^2 := by ring
    _ ≤ deltaB := div_le_self hdelta hLsq
    _ ≤ B.r := hdeltar
    _ = 2*(B.r/2) := by ring

theorem BranchEstimates.length_restrict {d : LocalBranchData} (B : BranchEstimates d)
    (ε : ℝ) (hε : 0 < ε) (hε₀ : ε ≤ B.ε₀) (S : Set ℝ) (hS : S ⊆ Icc (-B.r) B.r) :
    IntegrableOn (fun u => ‖deriv (originalPhase d ε) u‖) S volume ∧
    (∫ u in S, ‖deriv (originalPhase d ε) u‖) ≤ B.lengthC := by
  obtain ⟨hi,hb⟩ := B.length ε hε hε₀
  have hr := B.r_pos
  have hrr : -B.r ≤ B.r := by linarith
  have hi' : IntegrableOn (fun u => ‖deriv (originalPhase d ε) u‖) (Icc (-B.r) B.r) volume :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hrr).mp hi
  refine ⟨hi'.mono_set hS,?_⟩
  have hm := setIntegral_mono_set hi' (Filter.Eventually.of_forall fun _ => norm_nonneg _)
    hS.eventuallySubset
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hrr] at hm
  exact hm.trans hb

end
end IsingBulk.Branch
