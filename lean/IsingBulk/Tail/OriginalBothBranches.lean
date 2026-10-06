import IsingBulk.Tail.OriginalBranchMajorant
import IsingBulk.First.GlobalResidueRoot

/-! Both original inverse-dispersion branch arcs on one complex cε disk.
The upper arc is reduced to the lower outward-plateau estimate by y inversion.
No change of the physical root sheet is assumed. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Branch IsingBulk.First

def originalLowerPoint (c ε b u : ℝ) : ℂ :=
  Complex.exp ((-c*ε:ℝ)+((-b+u:ℝ):ℂ)*Complex.I)

def originalUpperPoint (c ε b u : ℝ) : ℂ :=
  Complex.exp ((-c*ε:ℝ)+((b+u:ℝ):ℂ)*Complex.I)

theorem plateau_upper_inverse (c ε τ b u : ℝ) (hτ : τ ≠ 0) :
    plateauY c ε τ (4*c*ε/τ) b (-u) = (originalUpperPoint c ε b u)⁻¹ := by
  have hv : -c*ε+τ*(4*c*ε/τ)/2=c*ε := by field_simp [hτ]; ring
  unfold plateauY originalUpperPoint
  rw [hv,← Complex.exp_neg]
  congr 1
  push_cast
  ring

theorem branch_dispersion_inverse (s y : ℂ) :
    IsingBulk.Branch.dispersion s y⁻¹=IsingBulk.Branch.dispersion s y := by
  unfold IsingBulk.Branch.dispersion
  rw [inv_inv]
  ring

/-- Actual source globalRoot and residueFactor, with one set of constants
for both branch signs and every complex parameter in the original disk. -/
theorem original_disk_both_branch_onebody (d : LocalBranchData) :
    ∃ C δ h ε₀ : ℝ, 0 < C ∧ 0 < δ ∧ 0 < h ∧ 0 < ε₀ ∧
    ∀ ε u : ℝ, ∀ s : ℂ, 0 < ε → ε < ε₀ → |u| < h →
      ‖s-radialParameter d.theta ε‖ ≤ δ*ε →
      (‖residueFactor (globalRoot s (originalLowerPoint d.c₀ ε d.thetaB u))‖ ≤
        C/Real.sqrt (|u|+ε)) ∧
      (‖residueFactor (globalRoot s (originalUpperPoint d.c₀ ε d.thetaB u))‖ ≤
        C/Real.sqrt (|u|+ε)) := by
  obtain ⟨C,δ,r,hC,hδ,hr,hm⟩ := original_disk_branch_onebody d
  have hc₀ := d.c₀_pos
  let τ := r/2
  have hτ : 0 < τ := half_pos hr
  let ε₀ := min r (τ/(4*d.c₀))
  have hε₀ : 0 < ε₀ := lt_min hr (div_pos hτ (by positivity))
  refine ⟨C,δ,r,ε₀,hC,hδ,hr,hε₀,?_⟩
  intro ε u s hε hεr hur hs
  have hεr' : ε < r := hεr.trans_le (min_le_left _ _)
  have ht : 0 ≤ 4*d.c₀*ε/τ := by positivity
  have ht1 : 4*d.c₀*ε/τ ≤ 1 := by
    apply (div_le_one hτ).mpr
    have he := hεr.le.trans (min_le_right r (τ/(4*d.c₀)))
    have hh := (le_div_iff₀ (show 0 < 4*d.c₀ by positivity)).mp he
    nlinarith
  constructor
  · have hl := hm 0 ε 0 u s le_rfl hr hε hεr' le_rfl zero_le_one hur hs
    simpa [globalRoot,sourceW,sourceS,IsingBulk.Branch.dispersion,
      originalLowerPoint,plateauY] using hl
  · have hu := hm τ ε (4*d.c₀*ε/τ) (-u) s hτ.le (half_lt_self hr)
      hε hεr' ht ht1 (by simpa using hur) hs
    rw [plateau_upper_inverse d.c₀ ε τ d.thetaB u hτ.ne',branch_dispersion_inverse] at hu
    simpa [globalRoot,sourceW,sourceS,IsingBulk.Branch.dispersion,abs_neg] using hu

end
end IsingBulk.Tail
