import IsingBulk.Tail.MicrocoreChartPoint
import IsingBulk.Analysis.BranchInclusion
import IsingBulk.First.RadialDiskAdmissibility

/-! Physical original-branch centers instantiate the complete microcore
chart with one neighborhood before the particle number. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Jets IsingBulk.Branch IsingBulk.Lie

theorem angularG_real_re (v θ u : ℝ) :
    (angularG v θ (u:ℂ)).re=-(Real.exp v+Real.exp (-v))*Real.sin (u-θ)/2 := by
  unfold angularG angularY
  rw [← Complex.exp_neg]
  simp [Complex.div_ofNat_re,Complex.mul_re,Complex.exp_im,Complex.mul_im,Real.sin_sub]
  ring

theorem angularG_real_re_pos (v θ u : ℝ) (hlo : -Real.pi < u-θ) (hhi : u-θ < 0) :
    0 < (angularG v θ (u:ℂ)).re := by
  rw [angularG_real_re]
  have hs : Real.sin (u-θ) < 0 := Real.sin_neg_of_neg_of_neg_pi_lt hhi hlo
  have hp : 0 < Real.exp v+Real.exp (-v) := add_pos (Real.exp_pos _) (Real.exp_pos _)
  nlinarith

theorem original_chartW_eq (d : LocalBranchData) (ε u : ℝ) :
    chartW (radialParameter d.theta ε) (-d.c₀*ε) d.thetaB (u:ℂ)=originalW d ε u := by
  rw [originalW_dispersion]
  unfold chartW angularY
  congr 2
  push_cast
  ring

theorem original_microcore_chart (d : LocalBranchData) :
    ∃ r : ℝ, 0 < r ∧ ∀ ε : ℝ, 0 < ε → ε < r → ∀ n : ℕ, ∀ x : AngularSpace n,
      (∀ i, |x i| < r) → MicrocoreJetPoint (-d.c₀*ε) d.thetaB (radialParameter d.theta ε) x := by
  obtain ⟨rB,hrB,hB⟩ := original_branch_inclusion d
  have hb := d.thetaB_pos
  have hp : 0 < Real.pi-d.thetaB := sub_pos.mpr d.thetaB_lt
  let r := min rB (min d.thetaB (Real.pi-d.thetaB))/2
  have hr : 0 < r := by dsimp [r]; positivity
  have hrr : r < rB ∧ r < d.thetaB ∧ r < Real.pi-d.thetaB := by
    have hh : r < min rB (min d.thetaB (Real.pi-d.thetaB)) := half_lt_self (by positivity)
    simpa only [lt_min_iff] using hh
  refine ⟨r,hr,?_⟩
  intro ε hε hεr n x hx
  have hs : radialParameter d.theta ε ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [IsingBulk.First.radialParameter_norm hε.le]
    linarith
  apply microcoreJetPoint_of_quadrants _ _ _ _ hs
  · intro i
    rw [original_chartW_eq]
    exact (hB ε (x i) hε (hεr.trans hrr.1) ((hx i).trans hrr.1)).1
  · intro i
    rw [original_chartW_eq]
    exact (hB ε (x i) hε (hεr.trans hrr.1) ((hx i).trans hrr.1)).2
  · intro i
    apply angularG_real_re_pos
    · have hh := (abs_lt.mp (hx i)).1
      linarith [hrr.2.2]
    · have hh := (abs_lt.mp (hx i)).2
      linarith [hrr.2.1]

end
end IsingBulk.Tail
