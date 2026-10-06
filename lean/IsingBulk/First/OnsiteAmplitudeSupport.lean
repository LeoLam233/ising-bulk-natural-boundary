import IsingBulk.First.OnsiteNormalizedJets

/-! Global angular smoothness and compact support of the actual generated
amplitude, using only inactive-factor separation on the fixed cutoff support. -/
namespace IsingBulk.First
noncomputable section
open Filter
open scoped Topology ContDiff

/-- A source jet is globally smooth in the real angles even if an inactive
rational denominator vanishes far outside the fixed angular cutoff. -/
theorem onsiteNormalizedAmplitude_contDiff {N : ℕ} (ρ v : ℂ) (r : ℝ) (s : ℂ)
    (w : DoubleAngularVector N → ℝ) (hw : ContDiff ℝ ∞ w)
    (J : Finset (SingularFactorIndex N)) (hr : r ≠ 0) (hs : s ≠ 0)
    (hden : ∀ u ∈ tsupport w, ∀ f ∈ Jᶜ,
      onsiteFactorDenominator s (angleTuple r u.1) (angleTuple r u.2) f ≠ 0) (j : ℕ) :
    ContDiff ℝ ∞ (onsiteNormalizedAmplitude ρ v r s w J j) := by
  rw [contDiff_iff_contDiffAt]
  intro u
  by_cases hu : u ∈ tsupport w
  · have h := onsiteNormalizedAmplitude_joint_contDiffAt w hw J ρ v r s u
      ⟨hr,hs,hden u hu⟩ j
    exact h.comp u
      (show ContDiffAt ℝ ∞ (fun a : DoubleAngularVector N => (((ρ,v),(r,a)),s)) u by fun_prop)
  · have hz := notMem_tsupport_iff_eventuallyEq.mp hu
    have he : onsiteNormalizedAmplitude ρ v r s w J j =ᶠ[𝓝 u] (fun _ => (0 : ℂ)) := by
      filter_upwards [hz] with a ha
      exact onsiteNormalizedAmplitude_eq_zero ρ v r s w J j a ha
    exact contDiffAt_const.congr_of_eventuallyEq he

/-- All generated amplitudes share the fixed original compact angular support. -/
theorem onsiteNormalizedAmplitude_hasCompactSupport {N : ℕ} (ρ v : ℂ) (r : ℝ) (s : ℂ)
    (w : DoubleAngularVector N → ℝ) (hw : HasCompactSupport w)
    (J : Finset (SingularFactorIndex N)) (j : ℕ) :
    HasCompactSupport (onsiteNormalizedAmplitude ρ v r s w J j) :=
  hw.of_isClosed_subset (isClosed_tsupport _) (onsiteNormalizedAmplitude_tsupport_subset ρ v r s w J j)

end
end IsingBulk.First
