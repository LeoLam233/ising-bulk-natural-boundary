import IsingBulk.Tail.CompactTruncatedIntegral

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Lie Set Filter Function MeasureTheory
open scoped Topology ContDiff BigOperators
set_option maxHeartbeats 1500000

/-- Finite rational pair partitions reconstruct every true parameter derivative.
Equality configurations are removed only as null sets at positive damping. -/
theorem compact_pair_derivative_reconstruction {n : ℕ}
    (f : SelectorFunctions) (hf : RegularSelector f) {r τ lam : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ) (hlam : 0 ≤ lam)
    (P : Finset (Fin (n+1) × Fin (n+1))) (M : ℕ)
    (hP : ∃ p ∈ P, p.1 ≠ p.2) (w : AngularSpace n → ℂ)
    (hw : ContDiff ℝ ∞ w) (hK : HasCompactSupport w) (J : ℕ)
    {s : ℂ} (hs : s ∈ dampingDomain r) :
    iteratedDeriv J (fun z => ∫ θ, w θ*pulledDensity f r τ lam z θ) s=
      ∑ p ∈ P, iteratedDeriv J (fun z => ∫ θ,
        (w θ*(compactPairWeight P M p.1 p.2 θ:ℂ))*pulledDensity f r τ lam z θ) s := by
  let K := tsupport w
  let F := fun θ : AngularSpace n => iteratedDeriv J (fun z => pulledDensity f r τ lam z θ) s
  have hsource := compactSource_density_smooth (Nat.succ_pos n) f hf hr hr1 hτ hlam
  have hF : ContinuousOn F K := by
    intro θ _
    exact (((hsource.iteratedDeriv (compactSourceDomain_isOpen (n+1) r) J (s,θ)
      ⟨hs,mem_univ θ⟩).1.comp θ (contDiffAt_const.prodMk contDiffAt_id)).continuousAt).continuousWithinAt
  have hFi : IntegrableOn F K := hF.integrableOn_compact hK
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hw.continuous.continuousOn
  let B := max 0 C
  have hB : 0 ≤ B := le_max_left _ _
  have hwb : ∀ᵐ θ ∂volume.restrict K, ‖w θ‖ ≤ B := by
    filter_upwards [ae_restrict_mem hK.measurableSet] with θ hθ
    exact (hC θ hθ).trans (le_max_right _ _)
  have hformula (v : AngularSpace n → ℂ) (hv : support v ⊆ K)
      (hvm : AEStronglyMeasurable v (volume.restrict K)) (hvb : ∀ᵐ θ ∂volume.restrict K, ‖v θ‖ ≤ B) :
      iteratedDeriv J (fun z => ∫ θ, v θ*pulledDensity f r τ lam z θ) s=∫ θ in K, v θ*F θ := by
    have he : (fun z => ∫ θ, v θ*pulledDensity f r τ lam z θ)=
        (fun z => ∫ θ in K, v θ*pulledDensity f r τ lam z θ) := by
      funext z
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro θ hθ
      rw [notMem_support.mp (fun hn => hθ (hv hn)),zero_mul]
    rw [he]
    exact smooth_parameter_bounded_weight_integral_iteratedDeriv hK
      (compactSourceDomain_isOpen (n+1) r) (dampingDomain_isOpen r) _ hsource
      (fun _ h => ⟨h.1,mem_univ _⟩) v hvm hB hvb J hs
  let W := fun p : Fin (n+1) × Fin (n+1) => fun θ => w θ*(compactPairWeight P M p.1 p.2 θ:ℂ)
  have hWm (p) : AEStronglyMeasurable (W p) (volume.restrict K) :=
    hw.continuous.aestronglyMeasurable.mul
      (Complex.measurable_ofReal.comp (compactPairWeight_measurable P M p.1 p.2)).aestronglyMeasurable
  have hWb (p) (hp : p ∈ P) : ∀ᵐ θ ∂volume.restrict K, ‖W p θ‖ ≤ B := by
    filter_upwards [hwb] with θ hθ
    have hrange := compactPairWeight_range P M hp θ
    simp only [W,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hrange.1]
    exact (mul_le_of_le_one_right (norm_nonneg _) hrange.2).trans hθ
  have hWeq (p) (hp : p ∈ P) := hformula (W p)
    (fun _ hθ => subset_tsupport w (mul_ne_zero_iff.mp hθ).1) (hWm p) (hWb p hp)
  rw [hformula w (subset_tsupport w) hw.continuous.aestronglyMeasurable hwb]
  trans ∑ p ∈ P, ∫ θ in K, W p θ*F θ
  · rw [← integral_finsetSum P (fun p hp => hFi.bdd_mul (hWm p) (hWb p hp))]
    apply integral_congr_ae
    obtain ⟨p,hp,hne⟩ := hP
    filter_upwards [ae_restrict_of_ae (allBranchExterior_ae_selected_distinct p.1 p.2 hne)] with θ hθ
    have hsum := compactPairWeight_sum P M θ (compactPairWeightDenom_selected_pos P M hp hθ).ne'
    simp only [W,← Finset.sum_mul,← Finset.mul_sum,← Complex.ofReal_sum,hsum,Complex.ofReal_one,mul_one]
  · exact Finset.sum_congr rfl (fun p hp => (hWeq p hp).symm)

theorem compact_pair_derivative_bound {n : ℕ}
    (f : SelectorFunctions) (hf : RegularSelector f) {r τ lam : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ) (hlam : 0 ≤ lam)
    (P : Finset (Fin (n+1) × Fin (n+1))) (M : ℕ)
    (hP : ∃ p ∈ P, p.1 ≠ p.2) (w : AngularSpace n → ℂ)
    (hw : ContDiff ℝ ∞ w) (hK : HasCompactSupport w) (J : ℕ)
    {s : ℂ} (hs : s ∈ dampingDomain r) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ p ∈ P, ‖iteratedDeriv J (fun z => ∫ θ,
      (w θ*(compactPairWeight P M p.1 p.2 θ:ℂ))*pulledDensity f r τ lam z θ) s‖ ≤ B) :
    ‖iteratedDeriv J (fun z => ∫ θ, w θ*pulledDensity f r τ lam z θ) s‖ ≤ (n+1:ℕ)^2*B := by
  rw [compact_pair_derivative_reconstruction f hf hr hr1 hτ hlam P M hP w hw hK J hs]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _p ∈ P, B := Finset.sum_le_sum hb
    _ = (P.card:ℝ)*B := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by
      have hh := Finset.card_le_univ P
      simpa only [Fintype.card_prod,Fintype.card_fin,pow_two,Nat.cast_mul] using
        (Nat.cast_le.mpr hh : (P.card:ℝ) ≤ Fintype.card (Fin (n+1) × Fin (n+1)))) hB

end
end IsingBulk.Tail
