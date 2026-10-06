import IsingBulk.Tail.OnePhaseSpectatorKernel
import IsingBulk.Tail.CompactPairCoordinates

namespace IsingBulk.Tail
noncomputable section
open Set MeasureTheory
open scoped BigOperators

def onePhaseSumMap {N : ℕ} (p : Fin N) (b : ℝ) (u : Fin N → ℝ) : Fin N → ℝ :=
  fun i => if i=p then (∑ j, u j)-(N:ℝ)*b else u i

def onePhaseSumDerivative {N : ℕ} (p : Fin N) : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) :=
  ContinuousLinearMap.pi (fun i => if i=p then coordinateSumLinear N else ContinuousLinearMap.proj i)

theorem onePhaseSum_hasFDerivAt {N : ℕ} (p : Fin N) (b : ℝ) (u : Fin N → ℝ) :
    HasFDerivAt (onePhaseSumMap p b) (onePhaseSumDerivative p) u := by
  unfold onePhaseSumMap onePhaseSumDerivative
  rw [hasFDerivAt_pi]
  intro i
  by_cases hip : i=p
  · simpa only [hip,ite_true,
      coordinateSumLinear_apply] using (coordinateSumLinear N).hasFDerivAt.sub_const ((N:ℝ)*b)
  · simp only [hip,ite_false]
    convert! (ContinuousLinearMap.proj i : (Fin N → ℝ) →L[ℝ] ℝ).hasFDerivAt (x := u) using 1

theorem onePhaseSum_det {N : ℕ} (p q : Fin N) (hpq : p ≠ q) :
    (onePhaseSumDerivative p).det=1 := by
  have he : onePhaseSumDerivative p=
      twoPhaseUpdateDeriv (coordinateSumLinear N) (ContinuousLinearMap.proj q) p q := by
    apply ContinuousLinearMap.ext
    intro u
    funext i
    by_cases hip : i=p
    · simp [onePhaseSumDerivative,twoPhaseUpdateDeriv,hip]
    · by_cases hiq : i=q <;> simp [onePhaseSumDerivative,twoPhaseUpdateDeriv,hip,hiq]
  rw [he,sumPhaseUpdate_det _ hpq]
  simp [pairDirection,hpq.symm]

theorem onePhaseSum_injective {N : ℕ} (p : Fin N) (b : ℝ) : Function.Injective (onePhaseSumMap p b) := by
  intro u v he
  have hsum : (∑ i, u i)=(∑ i, v i) := by
    have hh := congrFun he p
    simpa only [onePhaseSumMap,ite_true,sub_left_inj] using hh
  have hrest (i : Fin N) (hip : i ≠ p) : u i=v i := by
    simpa [onePhaseSumMap,hip] using congrFun he i
  have herase : (∑ i ∈ Finset.univ.erase p, u i)=(∑ i ∈ Finset.univ.erase p, v i) :=
    Finset.sum_congr rfl (fun i hi => hrest i (Finset.mem_erase.mp hi).1)
  funext i
  by_cases hip : i=p
  · subst i
    have hu := Finset.sum_erase_add Finset.univ u (Finset.mem_univ p)
    have hv := Finset.sum_erase_add Finset.univ v (Finset.mem_univ p)
    linarith
  · exact hrest i hip

theorem onePhaseSum_image {N : ℕ} (p : Fin N) (b R : ℝ) :
    onePhaseSumMap p b '' Icc (fun _ => -R) (fun _ => R) ⊆ onePhaseSpectatorBox p R b := by
  rintro _ ⟨u,hu,rfl⟩
  have hsum : |∑ i, u i| ≤ (N:ℝ)*R := by
    have hh := (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => abs_le.mpr ⟨hu.1 i,hu.2 i⟩))
    simpa using hh
  constructor <;> intro i
  all_goals
    by_cases hip : i=p
    · simp only [onePhaseSumMap,hip,ite_true]
      linarith [(abs_le.mp hsum).1,(abs_le.mp hsum).2]
    · first | simpa [onePhaseSpectatorBox,onePhaseSumMap,hip] using hu.1 i
            | simpa [onePhaseSpectatorBox,onePhaseSumMap,hip] using hu.2 i

theorem onePhaseSum_kernel_eq {N : ℕ} (p : Fin N) (b α : ℝ) (L : Fin N → ℝ → ℝ)
    (u : Fin N → ℝ) :
    onePhaseSpectatorKernel p α L (onePhaseSumMap p b u)=
      (phaseDenominator (Real.exp (-α)) ((∑ i, u i)-(N:ℝ)*b))⁻¹*
        ∏ i ∈ Finset.univ.erase p, L i (u i) := by
  unfold onePhaseSpectatorKernel
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ p)]
  simp only [ite_true,onePhaseSumMap]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  simp [(Finset.mem_erase.mp hi).1]

/-- Integrating the true sum phase preserves all spectator weights. -/
theorem one_phase_sum_weighted_integral {N : ℕ} (p q : Fin N) (hpq : p ≠ q)
    (L : Fin N → ℝ → ℝ) (C : Fin N → ℝ) (hL0 : ∀ i t, 0 ≤ L i t)
    {R b α : ℝ} (hR : 0 ≤ R) (hRπ : R ≤ Real.pi) (hα : 0 < α) (hα1 : α ≤ 1)
    (hL : ∀ i, ContinuousOn (L i) (Icc (-R) R))
    (hLint : ∀ i, (∫ t in Icc (-R) R, L i t) ≤ C i) :
    let f := fun u : Fin N → ℝ =>
      (phaseDenominator (Real.exp (-α)) ((∑ i, u i)-(N:ℝ)*b))⁻¹*
        ∏ i ∈ Finset.univ.erase p, L i (u i)
    IntegrableOn f (Icc (fun _ => -R) (fun _ => R)) ∧
    (∫ u in Icc (fun _ => -R) (fun _ => R), f u) ≤
      ((N:ℝ)*simpleKernelConstant*(1+|Real.log α|))*(∏ i ∈ Finset.univ.erase p, C i) := by
  have hk := one_phase_spectator_kernel_integral (b := b) p L C hL0 hR hRπ hα hα1 hL hLint
  have hc := injective_coordinate_weighted_coarea_on
    (S := Icc (fun _ : Fin N => -R) (fun _ => R)) measurableSet_Icc
    (onePhaseSumMap p b) (fun _ => onePhaseSumDerivative p)
    (fun u _ => (onePhaseSum_hasFDerivAt p b u).hasFDerivWithinAt)
    (onePhaseSum_injective p b).injOn (onePhaseSum_image p b R)
    (fun _ => 1) (onePhaseSpectatorKernel p α L) continuousOn_const
    (onePhaseSpectatorKernel_continuousOn p hα L hL)
    (onePhaseSpectatorKernel_nonneg p α L hL0) hk.1 (C := 1) zero_le_one
    (fun _ _ => zero_le_one) (fun _ _ => by rw [onePhaseSum_det p q hpq]; norm_num)
  simp only [one_mul,onePhaseSum_kernel_eq] at hc
  exact ⟨hc.1,hc.2.trans hk.2⟩

end
end IsingBulk.Tail
