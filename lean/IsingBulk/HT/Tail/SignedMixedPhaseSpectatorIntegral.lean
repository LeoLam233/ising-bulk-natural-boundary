import IsingBulk.Tail.MixedPhaseSpectatorIntegral
import IsingBulk.HT.Contour.SignedPositiveSpectators

namespace IsingBulk.HT.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Tail IsingBulk.HT.Lie IsingBulk.HT.Contour Set MeasureTheory Filter
open scoped Topology BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false

theorem shifted_mixedPhaseSpectatorKernel_continuousOn (ξ ζ : ℝ) {N : ℕ} (j q : Fin N) {a b : ℝ}
    (ha : 0<a) (hb : 0<b) (L : ℝ → ℝ) (hL : ContinuousOn L (Icc 0 (2*Real.pi))) :
    ContinuousOn (shiftedWeightedPhaseSpectatorKernel j q a b ξ ζ L) (mixedPhaseSpectatorBox j q) := by
  apply continuousOn_finsetProd
  intro i _
  by_cases hij : i=j
  · simp only [hij,ite_true]
    exact ((shiftedPhaseKernel_continuous ha ξ).comp (continuous_apply j)).continuousOn
  · by_cases hiq : i=q
    · subst i
      simp only [hij,ite_false,ite_true]
      exact ((shiftedPhaseKernel_continuous hb ζ).comp (show Continuous (fun x : Fin N → ℝ => x q) from continuous_apply q)).continuousOn
    · simp only [hij,hiq,ite_false]
      apply hL.comp (continuous_apply i).continuousOn
      intro x hx
      exact ⟨hx.1 i,by simpa [mixedPhaseSpectatorBox,hij,hiq] using hx.2 i⟩

/-- Two phase coordinates each cost one periodic logarithm; every other
coordinate pays only its one-dimensional spectator integral. -/
theorem shifted_mixed_phase_spectator_kernel_integral (ξ ζ : ℝ) {N : ℕ} {j q : Fin N} (hjq : j≠q)
    (L : ℝ → ℝ) (C : ℝ) (hL0 : ∀ t,0≤L t) {a b : ℝ}
    (ha : 0<a) (ha1 : a≤1) (hb : 0<b) (hb1 : b≤1)
    (hLc : ContinuousOn L (Icc 0 (2*Real.pi))) (hLint : (∫ t in Icc 0 (2*Real.pi),L t)≤C) :
    IntegrableOn (shiftedWeightedPhaseSpectatorKernel j q a b ξ ζ L) (mixedPhaseSpectatorBox j q) ∧
      (∫ x in mixedPhaseSpectatorBox j q,shiftedWeightedPhaseSpectatorKernel j q a b ξ ζ L x)≤
      ((N:ℝ)*simpleKernelConstant*(1+|Real.log a|))*
        ((N:ℝ)*simpleKernelConstant*(1+|Real.log b|))*C^(N-2) := by
  have hcont := shifted_mixedPhaseSpectatorKernel_continuousOn ξ ζ j q ha hb L hLc
  refine ⟨hcont.integrableOn_compact isCompact_Icc,?_⟩
  let h : Fin N → ℝ := fun i => if i=j then (N:ℝ)*(2*Real.pi) else if i=q then (N:ℝ)*Real.pi else 2*Real.pi
  let w : Fin N → ℝ → ℝ := fun i t => if i=j then shiftedPhaseKernel a ξ t
    else if i=q then shiftedPhaseKernel b ζ t else L t
  have hw (x : Fin N → ℝ) : shiftedWeightedPhaseSpectatorKernel j q a b ξ ζ L x=∏ i,w i (x i) := rfl
  have hmeasure : volume.restrict (mixedPhaseSpectatorBox j q)=
      Measure.pi (fun i => volume.restrict (Icc 0 (h i))) := by
    rw [mixedPhaseSpectatorBox,← Set.pi_univ_Icc,volume_pi,Measure.restrict_pi_pi]
  simp_rw [hw]
  rw [hmeasure,integral_fintype_prod_eq_prod]
  let A := (N:ℝ)*simpleKernelConstant*(1+|Real.log a|)
  let B := (N:ℝ)*simpleKernelConstant*(1+|Real.log b|)
  have haI : (∫ t in Icc 0 ((N:ℝ)*(2*Real.pi)),shiftedPhaseKernel a ξ t)≤A := by
    have hh := shifted_kernel_interval_integral ha ha1 ξ N (show 0≤(N:ℝ)*(2*Real.pi) by positivity) (by ring_nf; rfl)
    rw [intervalIntegral.integral_of_le (by positivity),← integral_Icc_eq_integral_Ioc] at hh
    exact hh
  have hbI : (∫ t in Icc 0 ((N:ℝ)*Real.pi),shiftedPhaseKernel b ζ t)≤B := by
    have hh := shifted_kernel_interval_integral hb hb1 ζ N (show 0≤(N:ℝ)*Real.pi by positivity)
      (by nlinarith [Real.pi_pos,(Nat.cast_nonneg N : (0:ℝ)≤N)])
    rw [intervalIntegral.integral_of_le (by positivity),← integral_Icc_eq_integral_Ioc] at hh
    exact hh
  calc
    _ ≤ ∏ i : Fin N,if i=j then A else if i=q then B else C := by
      apply Finset.prod_le_prod₀
      · intro i _
        apply integral_nonneg
        intro t
        dsimp [w]
        split_ifs <;> first | exact shiftedPhaseKernel_nonneg _ _ _ | exact hL0 _
      · intro i _
        by_cases hij : i=j
        · subst i; simpa [w,h] using haI
        · by_cases hiq : i=q
          · subst i; simpa [w,h,hjq.symm] using hbI
          · simpa [w,h,hij,hiq] using hLint
    _ = _ := prod_two_distinguished hjq A B C

end
end IsingBulk.HT.Tail
