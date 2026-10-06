import IsingBulk.Analysis.BranchDerivative
import IsingBulk.Tail.MixedHybridChart
import IsingBulk.Tail.SelectedFContinuation

/-! Root-rational compact mixed coefficients. Their continuation needs no
global compact logarithmic phase and permits compact roots outside the disk. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set

def mixedRootSlope (s y : ℂ) : ℂ :=
  selectedContinuedRoot s y*(y-y⁻¹)/((selectedContinuedRoot s y)^2-1)

def mixedRootTau (s y : ℂ) : ℂ :=
  -2*Complex.I*(1-(s^2)⁻¹)*selectedContinuedRoot s y/(1-(selectedContinuedRoot s y)^2)

theorem interiorRoot_sine_identity (W : ℂ) :
    1-(interiorRoot W)^2=2*Complex.I*Complex.sin (lowerArccos W)*interiorRoot W := by
  have hz := interiorRoot_nonzero W
  have hd : (interiorRoot W)⁻¹-interiorRoot W=2*Complex.I*Complex.sqrt (1-W^2) := by
    rw [interiorRoot,inv_inv,inverseCosineRoot_inverse]
    unfold inverseCosineRoot
    ring
  rw [sin_lowerArccos,← hd]
  field_simp

theorem mixedRootSlope_eq_source {s y : ℂ} (hW : 0<(sourceW s y).im) :
    mixedRootSlope s y=mixedSourceSlope s y := by
  let z := selectedContinuedRoot s y
  have hz : z≠0 := continuedRoot_nonzero _
  have hsin := mixedSourcePhase_sin_ne hW
  have he : 1-z^2=2*Complex.I*Complex.sin (mixedSourcePhase s y)*z := by
    rw [show z=interiorRoot (sourceW s y) from continuedRoot_eq_interiorRoot hW]
    exact interiorRoot_sine_identity _
  have hd : z^2-1= -2*Complex.I*Complex.sin (mixedSourcePhase s y)*z := by linear_combination -he
  change z*(y-y⁻¹)/(z^2-1)=_
  rw [hd,mixedSourceSlope]
  field_simp
  ring_nf
  simp [Complex.I_sq]

theorem mixedRootTau_eq_source {s y : ℂ} (hW : 0<(sourceW s y).im) :
    mixedRootTau s y=mixedSourceTau s y := by
  let z := selectedContinuedRoot s y
  have hz : z≠0 := continuedRoot_nonzero _
  have hsin := mixedSourcePhase_sin_ne hW
  have he : 1-z^2=2*Complex.I*Complex.sin (mixedSourcePhase s y)*z := by
    rw [show z=interiorRoot (sourceW s y) from continuedRoot_eq_interiorRoot hW]
    exact interiorRoot_sine_identity _
  change -2*Complex.I*(1-(s^2)⁻¹)*z/(1-z^2)=_
  rw [he,mixedSourceTau]
  field_simp

theorem selectedContinuedRoot_joint_analyticAt {s y : ℂ} (hs : s≠0) (hy : y≠0)
    (hW : sourceW s y ∈ continuedRootDomain) :
    AnalyticAt ℂ (fun p : ℂ × ℂ => selectedContinuedRoot p.1 p.2) (s,y) := by
  have hsA : AnalyticAt ℂ (fun p : ℂ × ℂ => p.1+p.1⁻¹) (s,y) := analyticAt_fst.add (analyticAt_fst.inv hs)
  have hyA : AnalyticAt ℂ (fun p : ℂ × ℂ => p.2+p.2⁻¹) (s,y) := analyticAt_snd.add (analyticAt_snd.inv hy)
  have hw : AnalyticAt ℂ (fun p : ℂ × ℂ => sourceW p.1 p.2) (s,y) := hsA.sub hyA.div_const
  exact (continuedRoot_analyticAt hW).comp (f := fun p : ℂ × ℂ => sourceW p.1 p.2) hw

theorem mixedRootCoefficients_analyticAt {s y : ℂ} (hs : s≠0) (hy : y≠0)
    (hW : sourceW s y ∈ continuedRootDomain) :
    AnalyticAt ℂ (fun p : ℂ × ℂ => mixedRootSlope p.1 p.2) (s,y) ∧
      AnalyticAt ℂ (fun p : ℂ × ℂ => mixedRootTau p.1 p.2) (s,y) := by
  have hz := selectedContinuedRoot_joint_analyticAt hs hy hW
  have hd : 1-(selectedContinuedRoot s y)^2≠0 := continuedRoot_residue_gap hW
  constructor
  · exact (hz.mul (analyticAt_snd.sub (analyticAt_snd.inv hy))).div
      ((hz.pow 2).sub analyticAt_const) (by intro h; apply hd; linear_combination -h)
  · exact (((analyticAt_const.mul (analyticAt_const.sub ((analyticAt_fst.pow 2).inv (pow_ne_zero 2 hs)))).mul hz)).div
      (analyticAt_const.sub (hz.pow 2)) hd

theorem compact_mixedRootCoefficients_finite_jets (K : Set (ℂ × ℂ)) (hK : IsCompact K)
    (hsource : ∀ p∈K,p.1≠0 ∧ p.2≠0 ∧ sourceW p.1 p.2∈continuedRootDomain) (j : ℕ) :
    ∃ C : ℝ,0<C ∧ ∀ p∈K,∀ k≤j,
      ‖iteratedFDeriv ℂ k (fun p : ℂ × ℂ => mixedRootSlope p.1 p.2) p‖≤C ∧
      ‖iteratedFDeriv ℂ k (fun p : ℂ × ℂ => mixedRootTau p.1 p.2) p‖≤C := by
  obtain ⟨C,hC,hCb⟩ := compact_finite_analytic_jets K hK _
    (fun p hp => (mixedRootCoefficients_analyticAt (hsource p hp).1 (hsource p hp).2.1 (hsource p hp).2.2).1) j
  obtain ⟨D,hD,hDb⟩ := compact_finite_analytic_jets K hK _
    (fun p hp => (mixedRootCoefficients_analyticAt (hsource p hp).1 (hsource p hp).2.1 (hsource p hp).2.2).2) j
  refine ⟨max C D,lt_of_lt_of_le hC (le_max_left _ _),?_⟩
  intro p hp k hk
  exact ⟨(hCb p hp k hk).trans (le_max_left _ _),(hDb p hp k hk).trans (le_max_right _ _)⟩

end
end IsingBulk.Tail
