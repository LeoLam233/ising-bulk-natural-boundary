import IsingBulk.HT.Lie.SignedCoarea
import IsingBulk.Tail.AllBranchSpectatorCoarea

namespace IsingBulk.HT.Contour
noncomputable section
open IsingBulk.Tail IsingBulk.HT.Lie Set MeasureTheory Filter
open scoped Topology BigOperators
def shiftedWeightedPhaseSpectatorKernel {N : ℕ} (p q : Fin N) (a b shiftY shiftZ : ℝ) (L : ℝ → ℝ)
    (x : Fin N → ℝ) : ℝ :=
  ∏ i, if i=p then shiftedPhaseKernel a shiftY (x i)
    else if i=q then shiftedPhaseKernel b shiftZ (x i) else L (x i)

theorem shiftedWeightedPhaseSpectatorKernel_nonneg {N : ℕ} (p q : Fin N) (a b shiftY shiftZ : ℝ) (L : ℝ → ℝ)
    (hL : ∀ t, 0 ≤ L t) (x : Fin N → ℝ) : 0 ≤ shiftedWeightedPhaseSpectatorKernel p q a b shiftY shiftZ L x := by
  apply Finset.prod_nonneg
  intro i _
  split_ifs <;> first | exact shiftedPhaseKernel_nonneg _ _ _ | exact hL _

theorem shiftedWeightedPhaseSpectatorKernel_continuousOn {N : ℕ} (p q : Fin N) {a b R : ℝ}
    (ha : 0 < a) (hb : 0 < b) (shiftY shiftZ : ℝ) (L : ℝ → ℝ) (hL : ContinuousOn L (Icc (-R) R)) :
    ContinuousOn (shiftedWeightedPhaseSpectatorKernel p q a b shiftY shiftZ L) (phaseSpectatorBox p q R) := by
  apply continuousOn_finsetProd
  intro i _
  by_cases hip : i=p
  · simp only [hip,ite_true]
    exact ((shiftedPhaseKernel_continuous ha shiftY).comp (continuous_apply p)).continuousOn
  · by_cases hiq : i=q
    · subst i
      simp only [hip,ite_false,ite_true]
      exact ((shiftedPhaseKernel_continuous hb shiftZ).comp (show Continuous (fun x : Fin N → ℝ => x q) from continuous_apply q)).continuousOn
    · simp only [hip,hiq,ite_false]
      apply hL.comp (continuous_apply i).continuousOn
      intro x hx
      exact ⟨by simpa [phaseSpectatorBox,hip,hiq] using hx.1 i,
        by simpa [phaseSpectatorBox,hip,hiq] using hx.2 i⟩

theorem shifted_weighted_phase_spectator_kernel_integral {N : ℕ} {i j : Fin N} (hij : i≠j)
    (shiftY shiftZ : ℝ) (L : ℝ → ℝ) (C : ℝ) ( _hC : 0 ≤ C) (hL0 : ∀ t, 0 ≤ L t)
    {R a b : ℝ} ( _hR : 0≤R) (ha : 0<a) (ha1 : a≤1) (hb : 0<b) (hb1 : b≤1)
    (hLc : ContinuousOn L (Icc (-R) R)) (hLint : (∫ t in Icc (-R) R, L t) ≤ C) :
    IntegrableOn (shiftedWeightedPhaseSpectatorKernel i j a b shiftY shiftZ L) (phaseSpectatorBox i j R) ∧
      (∫ x in phaseSpectatorBox i j R, shiftedWeightedPhaseSpectatorKernel i j a b shiftY shiftZ L x)≤
      ((N:ℝ)*simpleKernelConstant*(1+|Real.log a|))*
      ((N:ℝ)*simpleKernelConstant*(1+|Real.log b|))*C^(N-2) := by
  have hcont := shiftedWeightedPhaseSpectatorKernel_continuousOn i j ha hb shiftY shiftZ L hLc
  refine ⟨hcont.integrableOn_compact isCompact_Icc,?_⟩
  let h : Fin N → ℝ := fun l => if l=i ∨ l=j then (N:ℝ)*Real.pi else R
  let w : Fin N → ℝ → ℝ := fun l t => if l=i then shiftedPhaseKernel a shiftY t
    else if l=j then shiftedPhaseKernel b shiftZ t else L t
  have hw (x : Fin N → ℝ) : shiftedWeightedPhaseSpectatorKernel i j a b shiftY shiftZ L x=∏ l, w l (x l) := rfl
  have hmeasure : volume.restrict (phaseSpectatorBox i j R)=
      Measure.pi (fun l => volume.restrict (Icc (-h l) (h l))) := by
    rw [phaseSpectatorBox,← Set.pi_univ_Icc,volume_pi,Measure.restrict_pi_pi]
  simp_rw [hw]
  rw [hmeasure,integral_fintype_prod_eq_prod]
  let A := (N:ℝ)*simpleKernelConstant*(1+|Real.log a|)
  let B := (N:ℝ)*simpleKernelConstant*(1+|Real.log b|)
  have hNpi : 0≤(N:ℝ)*Real.pi := by positivity
  have haI : (∫ t in Icc (-(N:ℝ)*Real.pi) ((N:ℝ)*Real.pi), shiftedPhaseKernel a shiftY t)≤A := by
    have he := shifted_kernel_interval_integral ha ha1 shiftY N
      (show -(N:ℝ)*Real.pi≤(N:ℝ)*Real.pi by linarith)
      (show (N:ℝ)*Real.pi≤-(N:ℝ)*Real.pi+(N:ℝ)*(2*Real.pi) by ring_nf; rfl)
    rw [intervalIntegral.integral_of_le (show -(N:ℝ)*Real.pi≤(N:ℝ)*Real.pi by linarith),← integral_Icc_eq_integral_Ioc] at he
    exact he
  have hbI : (∫ t in Icc (-(N:ℝ)*Real.pi) ((N:ℝ)*Real.pi), shiftedPhaseKernel b shiftZ t)≤B := by
    have he := shifted_kernel_interval_integral hb hb1 shiftZ N
      (show -(N:ℝ)*Real.pi≤(N:ℝ)*Real.pi by linarith)
      (show (N:ℝ)*Real.pi≤-(N:ℝ)*Real.pi+(N:ℝ)*(2*Real.pi) by ring_nf; rfl)
    rw [intervalIntegral.integral_of_le (show -(N:ℝ)*Real.pi≤(N:ℝ)*Real.pi by linarith),← integral_Icc_eq_integral_Ioc] at he
    exact he
  calc
    _ ≤ ∏ l : Fin N, if l=i then A else if l=j then B else C := by
      apply Finset.prod_le_prod₀
      · intro l _
        apply integral_nonneg
        intro t
        dsimp [w]
        split_ifs <;> first | exact shiftedPhaseKernel_nonneg _ _ _ | exact hL0 _
      · intro l _
        by_cases hli : l=i
        · subst l; simpa [w,h,neg_mul] using haI
        · by_cases hlj : l=j
          · subst l; simpa [w,h,Ne.symm hij,neg_mul] using hbI
          · simp only [w,h,hli,hlj,ite_false,or_self]
            exact hLint
    _ = _ := prod_two_distinguished hij A B C

theorem shiftedWeightedPhaseSpectatorKernel_factorization {N : ℕ} (p q : Fin N) (hpq : p ≠ q)
    (a b shiftY shiftZ : ℝ) (L : ℝ → ℝ) (x : Fin N → ℝ) :
    shiftedWeightedPhaseSpectatorKernel p q a b shiftY shiftZ L x=shiftedTwoPhaseKernel a b shiftY shiftZ (x p,x q)*
      ∏ i ∈ (Finset.univ.erase p).erase q, L (x i) := by
  let w : Fin N → ℝ := fun i => if i=p then shiftedPhaseKernel a shiftY (x i)
    else if i=q then shiftedPhaseKernel b shiftZ (x i) else L (x i)
  have hq : q ∈ Finset.univ.erase p := Finset.mem_erase.mpr ⟨hpq.symm,Finset.mem_univ q⟩
  change (∏ i, w i)=_
  rw [← Finset.mul_prod_erase Finset.univ w (Finset.mem_univ p),
    ← Finset.mul_prod_erase (Finset.univ.erase p) w hq]
  have he : ∏ i ∈ (Finset.univ.erase p).erase q, w i=∏ i ∈ (Finset.univ.erase p).erase q, L (x i) := by
    apply Finset.prod_congr rfl
    intro i hi
    have hiq := (Finset.mem_erase.mp hi).1
    have hip := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
    simp [w,hip,hiq]
  rw [he]
  simp [w,shiftedTwoPhaseKernel,hpq.symm,mul_assoc]

end
end IsingBulk.HT.Contour
