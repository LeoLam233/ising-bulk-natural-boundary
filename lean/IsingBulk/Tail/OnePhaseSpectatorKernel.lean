import IsingBulk.Tail.AllBranchSpectatorCoarea

/-! A single periodic kernel with arbitrary nonnegative spectator weights.
The phase interval is translated, retaining its length independently of the shift. -/
namespace IsingBulk.Tail
noncomputable section
open Set MeasureTheory
open scoped BigOperators

def onePhaseSpectatorBox {N : ℕ} (p : Fin N) (R b : ℝ) : Set (Fin N → ℝ) :=
  Icc (fun i => if i=p then -(N:ℝ)*R-(N:ℝ)*b else -R)
    (fun i => if i=p then (N:ℝ)*R-(N:ℝ)*b else R)

def onePhaseSpectatorKernel {N : ℕ} (p : Fin N) (α : ℝ) (L : Fin N → ℝ → ℝ)
    (u : Fin N → ℝ) : ℝ :=
  ∏ i, if i=p then (phaseDenominator (Real.exp (-α)) (u i))⁻¹ else L i (u i)

theorem onePhaseSpectatorKernel_nonneg {N : ℕ} (p : Fin N) (α : ℝ) (L : Fin N → ℝ → ℝ)
    (hL : ∀ i t, 0 ≤ L i t) (u : Fin N → ℝ) : 0 ≤ onePhaseSpectatorKernel p α L u := by
  apply Finset.prod_nonneg
  intro i _
  split_ifs
  · exact inv_nonneg.mpr (norm_nonneg _)
  · exact hL i (u i)

theorem onePhaseSpectatorKernel_continuousOn {N : ℕ} (p : Fin N) {α R b : ℝ}
    (hα : 0 < α) (L : Fin N → ℝ → ℝ) (hL : ∀ i, ContinuousOn (L i) (Icc (-R) R)) :
    ContinuousOn (onePhaseSpectatorKernel p α L) (onePhaseSpectatorBox p R b) := by
  apply continuousOn_finsetProd
  intro i _
  by_cases hip : i=p
  · subst i
    simp only [ite_true]
    exact ((simple_kernel_continuous hα).comp (continuous_apply p)).continuousOn
  · simp only [hip,ite_false]
    exact (hL i).comp (continuous_apply i).continuousOn (fun u hu =>
      ⟨by simpa [onePhaseSpectatorBox,hip] using hu.1 i,
       by simpa [onePhaseSpectatorBox,hip] using hu.2 i⟩)

theorem one_phase_spectator_kernel_integral {N : ℕ} (p : Fin N)
    (L : Fin N → ℝ → ℝ) (C : Fin N → ℝ) (hL0 : ∀ i t, 0 ≤ L i t)
    {R b α : ℝ} (hR : 0 ≤ R) (hRπ : R ≤ Real.pi) (hα : 0 < α) (hα1 : α ≤ 1)
    (hL : ∀ i, ContinuousOn (L i) (Icc (-R) R))
    (hLint : ∀ i, (∫ t in Icc (-R) R, L i t) ≤ C i) :
    IntegrableOn (onePhaseSpectatorKernel p α L) (onePhaseSpectatorBox p R b) ∧
    (∫ u in onePhaseSpectatorBox p R b, onePhaseSpectatorKernel p α L u) ≤
      ((N:ℝ)*simpleKernelConstant*(1+|Real.log α|))*(∏ i ∈ Finset.univ.erase p, C i) := by
  refine ⟨(onePhaseSpectatorKernel_continuousOn p hα L hL).integrableOn_compact isCompact_Icc,?_⟩
  let lo := fun i : Fin N => if i=p then -(N:ℝ)*R-(N:ℝ)*b else -R
  let hi := fun i : Fin N => if i=p then (N:ℝ)*R-(N:ℝ)*b else R
  let w := fun i t => if i=p then (phaseDenominator (Real.exp (-α)) t)⁻¹ else L i t
  let A := (N:ℝ)*simpleKernelConstant*(1+|Real.log α|)
  have hmeasure : volume.restrict (onePhaseSpectatorBox p R b)=
      Measure.pi (fun i => volume.restrict (Icc (lo i) (hi i))) := by
    rw [onePhaseSpectatorBox,← Set.pi_univ_Icc,volume_pi,Measure.restrict_pi_pi]
  change (∫ u in onePhaseSpectatorBox p R b, ∏ i, w i (u i)) ≤ _
  rw [hmeasure,integral_fintype_prod_eq_prod]
  have hN : (0:ℝ) ≤ N := Nat.cast_nonneg _
  have horder : -(N:ℝ)*R-(N:ℝ)*b ≤ (N:ℝ)*R-(N:ℝ)*b := by nlinarith
  have hphase : (∫ t in Icc (-(N:ℝ)*R-(N:ℝ)*b) ((N:ℝ)*R-(N:ℝ)*b),
      (phaseDenominator (Real.exp (-α)) t)⁻¹) ≤ A := by
    have hh := simple_kernel_interval_integral hα hα1 N horder
      (show (N:ℝ)*R-(N:ℝ)*b ≤ -(N:ℝ)*R-(N:ℝ)*b+(N:ℝ)*(2*Real.pi) by nlinarith)
    rwa [intervalIntegral.integral_of_le horder,← integral_Icc_eq_integral_Ioc] at hh
  calc
    _ ≤ ∏ i : Fin N, if i=p then A else C i := by
      apply Finset.prod_le_prod₀
      · intro i _
        apply integral_nonneg
        intro t
        dsimp [w]
        split_ifs
        · exact inv_nonneg.mpr (norm_nonneg _)
        · exact hL0 i t
      · intro i _
        by_cases hip : i=p
        · subst i
          simpa [w,lo,hi] using hphase
        · simpa [w,lo,hi,hip] using hLint i
    _ = _ := by
      rw [← Finset.mul_prod_erase Finset.univ (fun i => if i=p then A else C i) (Finset.mem_univ p)]
      simp only [ite_true]
      congr 1
      apply Finset.prod_congr rfl
      intro i hi
      simp [(Finset.mem_erase.mp hi).1]

end
end IsingBulk.Tail
