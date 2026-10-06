import IsingBulk.Tail.MixedCoordinatePhase
import IsingBulk.Tail.AllBranchSpectatorCoarea

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First Set MeasureTheory
open scoped BigOperators

def mixedPhaseSpectatorBox {N : ℕ} (j q : Fin N) : Set (Fin N → ℝ) :=
  Icc (fun _ => 0) (fun i => if i=j then (N:ℝ)*(2*Real.pi) else if i=q then (N:ℝ)*Real.pi else 2*Real.pi)

theorem mixedCoordinatePhase_image {N : ℕ} (f : SelectorFunctions) (r τ lam : ℝ) (s : ℂ)
    (j q : Fin N) {S : Set (Fin N → ℝ)}
    (hbox : S⊆angleBox N)
    (hW : ∀ θ∈S,∀ i,0<(sourceW s (deformedPoint f r τ lam θ i)).im) :
    mixedCoordinatePhase f r τ lam s j q '' S⊆mixedPhaseSpectatorBox j q := by
  rintro _ ⟨θ,hθ,rfl⟩
  have hF0 : 0≤∑ i,θ i := Finset.sum_nonneg (fun i _ => (hbox hθ).1 i)
  have hF1 : (∑ i,θ i)≤(N:ℝ)*(2*Real.pi) := by
    simpa using Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => (hbox hθ).2 i)
  have hG := mixedPhaseSum_bounds f r τ lam s θ (hW θ hθ)
  constructor <;> intro i
  all_goals
    by_cases hij : i=j
    · subst i
      first | simpa [mixedCoordinatePhase,twoPhaseUpdate,mixedPhaseSpectatorBox] using hF0
            | simpa [mixedCoordinatePhase,twoPhaseUpdate,mixedPhaseSpectatorBox] using hF1
    · by_cases hiq : i=q
      · subst i
        first | simpa [mixedCoordinatePhase,twoPhaseUpdate,mixedPhaseSpectatorBox,hij] using hG.1
              | simpa [mixedCoordinatePhase,twoPhaseUpdate,mixedPhaseSpectatorBox,hij] using hG.2
      · first | simpa [mixedCoordinatePhase,twoPhaseUpdate,mixedPhaseSpectatorBox,hij,hiq] using (hbox hθ).1 i
              | simpa [mixedCoordinatePhase,twoPhaseUpdate,mixedPhaseSpectatorBox,hij,hiq] using (hbox hθ).2 i

theorem mixedPhaseSpectatorKernel_continuousOn {N : ℕ} (j q : Fin N) {a b : ℝ}
    (ha : 0<a) (hb : 0<b) (L : ℝ → ℝ) (hL : ContinuousOn L (Icc 0 (2*Real.pi))) :
    ContinuousOn (weightedPhaseSpectatorKernel j q a b L) (mixedPhaseSpectatorBox j q) := by
  apply continuousOn_finsetProd
  intro i _
  by_cases hij : i=j
  · simp only [hij,ite_true]
    exact ((simple_kernel_continuous ha).comp (continuous_apply j)).continuousOn
  · by_cases hiq : i=q
    · subst i
      simp only [hij,ite_false,ite_true]
      exact ((simple_kernel_continuous hb).comp (show Continuous (fun x : Fin N → ℝ => x q) from continuous_apply q)).continuousOn
    · simp only [hij,hiq,ite_false]
      apply hL.comp (continuous_apply i).continuousOn
      intro x hx
      exact ⟨hx.1 i,by simpa [mixedPhaseSpectatorBox,hij,hiq] using hx.2 i⟩

/-- Two phase coordinates each cost one periodic logarithm; every other
coordinate pays only its one-dimensional spectator integral. -/
theorem mixed_phase_spectator_kernel_integral {N : ℕ} {j q : Fin N} (hjq : j≠q)
    (L : ℝ → ℝ) (C : ℝ) (hL0 : ∀ t,0≤L t) {a b : ℝ}
    (ha : 0<a) (ha1 : a≤1) (hb : 0<b) (hb1 : b≤1)
    (hLc : ContinuousOn L (Icc 0 (2*Real.pi))) (hLint : (∫ t in Icc 0 (2*Real.pi),L t)≤C) :
    IntegrableOn (weightedPhaseSpectatorKernel j q a b L) (mixedPhaseSpectatorBox j q) ∧
      (∫ x in mixedPhaseSpectatorBox j q,weightedPhaseSpectatorKernel j q a b L x)≤
      ((N:ℝ)*simpleKernelConstant*(1+|Real.log a|))*
        ((N:ℝ)*simpleKernelConstant*(1+|Real.log b|))*C^(N-2) := by
  have hcont := mixedPhaseSpectatorKernel_continuousOn j q ha hb L hLc
  refine ⟨hcont.integrableOn_compact isCompact_Icc,?_⟩
  let h : Fin N → ℝ := fun i => if i=j then (N:ℝ)*(2*Real.pi) else if i=q then (N:ℝ)*Real.pi else 2*Real.pi
  let w : Fin N → ℝ → ℝ := fun i t => if i=j then (phaseDenominator (Real.exp (-a)) t)⁻¹
    else if i=q then (phaseDenominator (Real.exp (-b)) t)⁻¹ else L t
  have hw (x : Fin N → ℝ) : weightedPhaseSpectatorKernel j q a b L x=∏ i,w i (x i) := rfl
  have hmeasure : volume.restrict (mixedPhaseSpectatorBox j q)=
      Measure.pi (fun i => volume.restrict (Icc 0 (h i))) := by
    rw [mixedPhaseSpectatorBox,← Set.pi_univ_Icc,volume_pi,Measure.restrict_pi_pi]
  simp_rw [hw]
  rw [hmeasure,integral_fintype_prod_eq_prod]
  let A := (N:ℝ)*simpleKernelConstant*(1+|Real.log a|)
  let B := (N:ℝ)*simpleKernelConstant*(1+|Real.log b|)
  have haI : (∫ t in Icc 0 ((N:ℝ)*(2*Real.pi)),(phaseDenominator (Real.exp (-a)) t)⁻¹)≤A := by
    have hh := simple_kernel_interval_integral ha ha1 N (show 0≤(N:ℝ)*(2*Real.pi) by positivity) (by ring_nf; rfl)
    rw [intervalIntegral.integral_of_le (by positivity),← integral_Icc_eq_integral_Ioc] at hh
    exact hh
  have hbI : (∫ t in Icc 0 ((N:ℝ)*Real.pi),(phaseDenominator (Real.exp (-b)) t)⁻¹)≤B := by
    have hh := simple_kernel_interval_integral hb hb1 N (show 0≤(N:ℝ)*Real.pi by positivity)
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
        split_ifs <;> first | exact inv_nonneg.mpr (norm_nonneg _) | exact hL0 _
      · intro i _
        by_cases hij : i=j
        · subst i; simpa [w,h] using haI
        · by_cases hiq : i=q
          · subst i; simpa [w,h,hjq.symm] using hbI
          · simpa [w,h,hij,hiq] using hLint
    _ = _ := prod_two_distinguished hjq A B C

end
end IsingBulk.Tail
