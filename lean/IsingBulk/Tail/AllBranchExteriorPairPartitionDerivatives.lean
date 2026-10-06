import IsingBulk.Tail.AllBranchExteriorWeightedJets
import IsingBulk.Tail.AllBranchExteriorTruncationIntegralLimit

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Jets IsingBulk.Lie MeasureTheory Set Filter Function
open scoped Topology ContDiff BigOperators

theorem allBranchExterior_pair_partition_derivatives (d : LocalBranchData) :
    ∃ r : ℝ, 0 < r ∧ ∀ ε : ℝ, 0 < ε → ε ≤ r → ∀ n : ℕ, 1 ≤ n →
      ∀ M : ℕ, ∀ w : AngularSpace n → ℝ, ContDiff ℝ ∞ w →
      tsupport w ⊆ microcoreCube (n+1) r → ∀ j : ℕ,
      iteratedDeriv j (allBranchOriginalWeightedIntegral n d ε w) (radialParameter d.theta ε) =
        ∑ pq ∈ orderedIndexPairs (Finset.univ : Finset (Fin (n+1))),
          iteratedDeriv j (allBranchOriginalWeightedIntegral n d ε
            (fun u => w u*allBranchExteriorPairWeight M pq.1 pq.2 u)) (radialParameter d.theta ε) := by
  classical
  obtain ⟨r,hr,hjet⟩ := allBranchExterior_weighted_jet_representation d
  refine ⟨r,hr,?_⟩
  intro ε hε hεr n hn M w hw hsupp j
  let K := microcoreCube (n+1) r
  have hK : IsCompact K := microcoreCube_compact (n+1) r
  obtain ⟨f,hf,hrep⟩ := hjet ε hε hεr n j
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hw.continuous.continuousOn
  let B := max 0 C
  have hB : 0 ≤ B := le_max_left _ _
  have hwB (u : AngularSpace n) (hu : u ∈ K) : |w u| ≤ B := by
    have hh : |w u| ≤ C := by simpa only [Real.norm_eq_abs] using hC u hu
    exact hh.trans (le_max_right 0 C)
  let P := orderedIndexPairs (Finset.univ : Finset (Fin (n+1)))
  let W := fun pq : Fin (n+1) × Fin (n+1) => fun u => w u*allBranchExteriorPairWeight M pq.1 pq.2 u
  have hne (pq : Fin (n+1) × Fin (n+1)) (hpq : pq ∈ P) : pq.1 ≠ pq.2 := by
    exact ne_of_lt (Finset.mem_filter.mp hpq).2
  have hWm (pq : Fin (n+1) × Fin (n+1)) : Measurable (W pq) :=
    hw.continuous.measurable.mul (allBranchExterior_pairWeight_measurable M pq.1 pq.2)
  have hWs (pq : Fin (n+1) × Fin (n+1)) : support (W pq) ⊆ K := by
    intro u hu
    exact hsupp (subset_tsupport w (mul_ne_zero_iff.mp hu).1)
  have hWb (pq : Fin (n+1) × Fin (n+1)) (hpq : pq ∈ P) (u : AngularSpace n) (hu : u ∈ K) : |W pq u| ≤ B := by
    dsimp [W]
    rw [abs_mul,abs_of_nonneg (allBranchExterior_pairWeight_nonneg M pq.1 pq.2 u)]
    have hh : |w u| * allBranchExteriorPairWeight M pq.1 pq.2 u ≤ |w u| := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (allBranchExterior_pairWeight_le_one M pq.1 pq.2 (hne pq hpq) u) (abs_nonneg (w u))
    exact hh.trans (hwB u hu)
  have hWi (pq : Fin (n+1) × Fin (n+1)) (hpq : pq ∈ P) :
      IntegrableOn (fun u => (W pq u:ℂ)*f u) K := by
    apply (hf.integrableOn_compact hK).bdd_mul (Complex.measurable_ofReal.comp (hWm pq)).aestronglyMeasurable
    filter_upwards [ae_restrict_mem hK.measurableSet] with u hu
    simpa only [Function.comp_apply,Complex.norm_real,Real.norm_eq_abs] using hWb pq hpq u hu
  have hsum : (∫ u in K, (w u:ℂ)*f u) = ∑ pq ∈ P, ∫ u in K, (W pq u:ℂ)*f u := by
    rw [← integral_finsetSum P hWi]
    apply integral_congr_ae
    have hneq : (⟨0,by omega⟩ : Fin (n+1)) ≠ ⟨1,by omega⟩ := by simp
    filter_upwards [ae_restrict_of_ae (allBranchExterior_ae_selected_distinct _ _ hneq)] with u hu
    have hdiam : 0 < allBranchExteriorDiameter u :=
      (abs_pos.mpr (sub_ne_zero.mpr hu)).trans_le (allBranchExterior_pair_le_diameter u _ _)
    have hpart := allBranchExterior_pairWeight_sum M u hdiam
    simp only [W,Complex.ofReal_mul,← Finset.sum_mul,← Finset.mul_sum,← Complex.ofReal_sum]
    rw [hpart,Complex.ofReal_one,mul_one]
  rw [hrep w hw.continuous.measurable (fun u hu => hsupp (subset_tsupport w hu)) B hB hwB,hsum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro pq hpq
  exact (hrep (W pq) (hWm pq) (hWs pq) B hB (hWb pq hpq)).symm

theorem allBranchExterior_pair_partition_bound (d : LocalBranchData) :
    ∃ r : ℝ, 0 < r ∧ ∀ ε : ℝ, 0 < ε → ε ≤ r → ∀ n : ℕ, 1 ≤ n →
      ∀ M : ℕ, ∀ w : AngularSpace n → ℝ, ContDiff ℝ ∞ w →
      tsupport w ⊆ microcoreCube (n+1) r → ∀ j : ℕ, ∀ C : ℝ,
      (∀ p q : Fin (n+1), p ≠ q →
        ‖iteratedDeriv j (allBranchOriginalWeightedIntegral n d ε
          (fun u => w u*allBranchExteriorPairWeight M p q u)) (radialParameter d.theta ε)‖ ≤ C) →
      ‖iteratedDeriv j (allBranchOriginalWeightedIntegral n d ε w) (radialParameter d.theta ε)‖ ≤
        ((n+1).choose 2:ℝ)*C := by
  obtain ⟨r,hr,hpart⟩ := allBranchExterior_pair_partition_derivatives d
  refine ⟨r,hr,?_⟩
  intro ε hε hεr n hn M w hw hsupp j C hC
  rw [hpart ε hε hεr n hn M w hw hsupp j]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _pq ∈ orderedIndexPairs (Finset.univ : Finset (Fin (n+1))), C :=
      Finset.sum_le_sum (fun pq hpq => hC pq.1 pq.2 (ne_of_lt (Finset.mem_filter.mp hpq).2))
    _ = _ := by simp [orderedIndexPairs_card]

end
end IsingBulk.Tail
