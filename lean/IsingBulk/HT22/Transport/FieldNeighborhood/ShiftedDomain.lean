import IsingBulk.HT22.Transport.FieldNeighborhood.CompactInputs
import IsingBulk.Preferred22.RightDomain

/-! Fixed-v inverse jets on the genuine source regular domain.
The moving coordinate is translated explicitly. In particular fixed-q
parameter derivatives are never identified with fixed-v derivatives. -/
namespace IsingBulk.HT22
noncomputable section
open Set Metric Geometry IsingBulk.Preferred22
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

theorem regularInverse_joint_analytic_of_moving (t q : ℂ)
    (hB : AnalyticAt ℂ preferredMovingBranch t)
    (hU : AnalyticAt ℂ (fun z : ℂ × ℂ => preferredMovingInverse z.1 z.2) (t,q)) :
    AnalyticAt ℂ (fun z : ℂ × ℂ => regularInverse z.1 z.2)
      (t,q+preferredMovingBranch t) := by
  have hmap : AnalyticAt ℂ (fun z : ℂ × ℂ => (z.1,z.2-preferredMovingBranch z.1))
      (t,q+preferredMovingBranch t) :=
    analyticAt_fst.prod (analyticAt_snd.sub (AnalyticAt.comp (f := fun z : ℂ × ℂ => z.1)
      (g := preferredMovingBranch) hB analyticAt_fst))
  have hU' : AnalyticAt ℂ (fun z : ℂ × ℂ => preferredMovingInverse z.1 z.2)
      (t,(q+preferredMovingBranch t)-preferredMovingBranch t) := by
    simpa only [add_sub_cancel_right] using hU
  have ha := AnalyticAt.comp (f := fun z : ℂ × ℂ => (z.1,z.2-preferredMovingBranch z.1))
    (g := fun z : ℂ × ℂ => preferredMovingInverse z.1 z.2) hU' hmap
  simpa only [Function.comp_def,regularInverse_moving_adapter] using ha

/-- A source compact product is mapped to the unshifted coordinates. This
is an exact image, not a rectangular superset across a branch cut. -/
def inverseShiftImage (t₀ : ℂ) (ρ : ℝ) (D : Set ℂ) : Set (ℂ × ℂ) :=
  (fun z : ℂ × ℂ => (z.1,z.2+preferredMovingBranch z.1)) ''
    (closedBall t₀ ρ ×ˢ D)

theorem inverseShiftImage_compact (t₀ : ℂ) (ρ : ℝ) (D : Set ℂ)
    (hD : IsCompact D)
    (hB : ∀ t∈closedBall t₀ ρ, AnalyticAt ℂ preferredMovingBranch t) :
    IsCompact (inverseShiftImage t₀ ρ D) := by
  apply ((isCompact_closedBall t₀ ρ).prod hD).image_of_continuousOn
  intro z hz
  exact (continuousAt_fst.prodMk (continuousAt_snd.add
    ((hB z.1 hz.1).continuousAt.comp continuousAt_fst))).continuousWithinAt

/-- Uniform fixed-v parameter partial and their first joint jets, with a
constant chosen before N and before the actual occupancies. -/
theorem sourceInversePartials_uniform_shift_bound (t₀ : ℂ) (ρ : ℝ) (D : Set ℂ)
    (hD : IsCompact D)
    (hB : ∀ t∈closedBall t₀ ρ, AnalyticAt ℂ preferredMovingBranch t)
    (hU : ∀ t∈closedBall t₀ ρ, ∀ q∈D,
      AnalyticAt ℂ (fun z : ℂ × ℂ => preferredMovingInverse z.1 z.2) (t,q)) :
    ∃ C : ℝ, 0<C ∧ ∀ t q : ℂ, t∈closedBall t₀ ρ → q∈D →
      AnalyticAt ℂ (fun z : ℂ × ℂ => regularInverse z.1 z.2)
        (t,q+preferredMovingBranch t) ∧
      ‖sourceInverseT t (q+preferredMovingBranch t)‖≤C ∧
      ‖fderiv ℂ (fun z : ℂ × ℂ => sourceInverseV z.1 z.2)
        (t,q+preferredMovingBranch t)‖≤C ∧
      ‖fderiv ℂ (fun z : ℂ × ℂ => sourceInverseT z.1 z.2)
        (t,q+preferredMovingBranch t)‖≤C := by
  have ha : ∀ z∈inverseShiftImage t₀ ρ D,
      AnalyticAt ℂ (fun p : ℂ × ℂ => regularInverse p.1 p.2) z := by
    rintro z ⟨⟨t,q⟩,⟨ht,hq⟩,rfl⟩
    exact regularInverse_joint_analytic_of_moving t q (hB t ht) (hU t ht q hq)
  obtain ⟨C,hC,hbound⟩ := sourceInversePartials_compact_bound
    (inverseShiftImage t₀ ρ D) (inverseShiftImage_compact t₀ ρ D hD hB) ha
  refine ⟨C,hC,?_⟩
  intro t q ht hq
  have hm : (t,q+preferredMovingBranch t)∈inverseShiftImage t₀ ρ D :=
    ⟨(t,q),⟨ht,hq⟩,rfl⟩
  exact ⟨ha _ hm,hbound _ hm⟩

end
end IsingBulk.HT22
