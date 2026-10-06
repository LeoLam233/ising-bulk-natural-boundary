import IsingBulk.Tail.AllBranchExteriorWeightedIntegral
import IsingBulk.Tail.AllBranchExteriorSingleTruncation
import IsingBulk.Tail.AllBranchExteriorTruncationLimit
import IsingBulk.Tail.AllBranchExteriorWeightRange

/-! The selected-pair puncture can be removed in the actual original integral
at every parameter derivative order. This is a fixed-epsilon limit, with no
quantitative uniform-in-epsilon bound supplied as an assumption. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Jets IsingBulk.Lie MeasureTheory Set Filter Function
open scoped Topology ContDiff

theorem allBranchGuardedPairWeight_range {N : ℕ} (M : ℕ) (h : ℝ)
    (p q : Fin N) (hpq : p ≠ q) (u : Fin N → ℝ) :
    0 ≤ allBranchGuardedPairWeight M h p q u ∧ allBranchGuardedPairWeight M h p q u ≤ 1 := by
  have hp := allBranchExterior_pairWeight_nonneg M p q u
  have hp1 := allBranchExterior_pairWeight_le_one M p q hpq u
  have hg := allBranchSelectedGuard_range h p q u
  exact ⟨mul_nonneg hp hg.1,by
    simpa only [allBranchGuardedPairWeight,one_mul] using mul_le_mul hp1 hg.2 hg.1 (by norm_num : (0:ℝ) ≤ 1)⟩

theorem allBranchSingleTruncatedWeight_abs_le {N : ℕ} (M : ℕ) (h : ℝ)
    (p q : Fin N) (hpq : p ≠ q) (w : (Fin N → ℝ) → ℝ) (u : Fin N → ℝ) :
    |allBranchSingleTruncatedWeight M h p q w u| ≤ |w u| := by
  have hg := allBranchGuardedPairWeight_range M h p q hpq u
  rw [allBranchSingleTruncatedWeight,abs_mul,abs_of_nonneg hg.1]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hg.2 (abs_nonneg (w u))

theorem allBranchExterior_single_truncation_eventually {N : ℕ} (M : ℕ) (p q : Fin N)
    (w : (Fin N → ℝ) → ℝ) (u : Fin N → ℝ) (hu : u p ≠ u q) :
    ∀ᶠ k in atTop, allBranchSingleTruncatedWeight M (allBranchTruncationScale k) p q w u =
      w u*allBranchExteriorPairWeight M p q u := by
  have hδ : 0 < |u p-u q| := abs_pos.mpr (sub_ne_zero.mpr hu)
  filter_upwards [allBranchTruncationScale_tendsto.eventually (gt_mem_nhds hδ)] with k hk
  have hh := allBranchTruncationScale_pos k
  have hz : microCutoffBase ((u p-u q)/allBranchTruncationScale k)=0 := by
    by_contra hn
    have hb := fixedBranchBump_support 1 (by norm_num) hn
    rw [abs_div,abs_of_pos hh] at hb
    have ht := (div_lt_iff₀ hh).mp hb
    linarith
  simp [allBranchSingleTruncatedWeight,allBranchGuardedPairWeight,allBranchSelectedGuard,hz]

theorem allBranchExterior_single_truncation_derivatives_tendsto (d : LocalBranchData) :
    ∃ r : ℝ, 0 < r ∧ ∀ ε : ℝ, 0 < ε → ε ≤ r → ∀ n M : ℕ,
      ∀ p q : Fin (n+1), p ≠ q → ∀ w : AngularSpace n → ℝ,
      ContDiff ℝ ∞ w → tsupport w ⊆ microcoreCube (n+1) r → ∀ j : ℕ,
      Tendsto (fun k => iteratedDeriv j (allBranchOriginalWeightedIntegral n d ε
        (allBranchSingleTruncatedWeight M (allBranchTruncationScale k) p q w)) (radialParameter d.theta ε))
        atTop (𝓝 (iteratedDeriv j (allBranchOriginalWeightedIntegral n d ε
          (fun u => w u*allBranchExteriorPairWeight M p q u)) (radialParameter d.theta ε))) := by
  obtain ⟨r,hr,hdata⟩ := allBranchExterior_original_density_data d
  refine ⟨r,hr,?_⟩
  intro ε hε hεr n M p q hpq w hw hsupp j
  let K := microcoreCube (n+1) r
  have hK : IsCompact K := microcoreCube_compact (n+1) r
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hw.continuous.continuousOn
  have hwB (u : AngularSpace n) (hu : u ∈ K) : |w u| ≤ max 0 C := by
    simpa only [Real.norm_eq_abs] using (hC u hu).trans (le_max_right 0 C)
  have hlimabs (u : AngularSpace n) : |w u*allBranchExteriorPairWeight M p q u| ≤ |w u| := by
    rw [abs_mul,abs_of_nonneg (allBranchExterior_pairWeight_nonneg M p q u)]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (allBranchExterior_pairWeight_le_one M p q hpq u) (abs_nonneg (w u))
  apply allBranchExterior_weighted_derivatives_tendsto d ε hε _ K hK
    (fun u hu => (hdata ε hε hεr n u ((mem_microcoreCube r u).mp hu)).1)
    (fun u hu => (hdata ε hε hεr n u ((mem_microcoreCube r u).mp hu)).2)
    (fun k => allBranchSingleTruncatedWeight M (allBranchTruncationScale k) p q w)
    (fun u => w u*allBranchExteriorPairWeight M p q u)
    (fun k => (allBranchSingleTruncatedWeight_smooth M (allBranchTruncationScale_pos k) p q w hw).continuous.measurable)
    (hw.continuous.measurable.mul (allBranchExterior_pairWeight_measurable M p q))
    _ _ (le_max_left 0 C) _ _ _ j
  · intro k u hu
    apply hsupp (subset_tsupport w ?_)
    intro hz
    exact hu (by simp [allBranchSingleTruncatedWeight,hz])
  · intro u hu
    apply hsupp (subset_tsupport w ?_)
    exact (mul_ne_zero_iff.mp hu).1
  · intro k
    filter_upwards [ae_restrict_mem hK.measurableSet] with u hu
    exact (allBranchSingleTruncatedWeight_abs_le M _ p q hpq w u).trans (hwB u hu)
  · filter_upwards [ae_restrict_mem hK.measurableSet] with u hu
    exact (hlimabs u).trans (hwB u hu)
  · filter_upwards [ae_restrict_of_ae (allBranchExterior_ae_selected_distinct p q hpq)] with u hu
    apply tendsto_const_nhds.congr'
    filter_upwards [allBranchExterior_single_truncation_eventually M p q w u hu] with k hk
    exact hk.symm

end
end IsingBulk.Tail
