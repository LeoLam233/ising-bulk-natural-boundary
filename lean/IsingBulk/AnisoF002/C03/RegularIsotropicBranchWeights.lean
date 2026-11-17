import IsingBulk.AnisoF002.C03.RegularIsotropicMixedAttenuation
import IsingBulk.AnisoF002.C03.RegularIsotropicWeightedMatching

/-!
# Actual branch-coordinate weights and their complete matching cost

The number of true branch coordinates is bounded by the actual raw
populations. Their vertex weights have total cost at most exp(N/2),
uniformly even when the branch population is small. This bound retains
all coordinates and is independent of particle parity.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set
open scoped Topology BigOperators Classical

theorem upper_branch_plateau_window (b η u : ℝ) (hη : 0 < η)
    (hwidth : 4 * η ≤ Real.sin b) (hu : |u| ≤ η) :
    upperPeriodicBump η (b + u) = 1 ∧ lowerPeriodicBump η (b + u) = 0 := by
  have h := lower_branch_plateau_window b η (-u) hη hwidth (by simpa only [abs_neg] using hu)
  have hneg : -b + -u = -(b + u) := by ring
  rw [hneg] at h
  constructor
  · simpa only [lowerPeriodicBump, neg_neg] using h.2
  · exact h.1

def mixedBranchCoordinates {N : ℕ} (b δ : ℝ) (θ : Fin N → ℝ) : Finset (Fin N) :=
  Finset.univ.filter fun i => |θ i + b| ≤ δ ∨ |θ i - b| ≤ δ

theorem mixedBranchCoordinates_card_le_population {N : ℕ} (b η δ : ℝ)
    (hη : 0 < η) (hwidth : 4 * η ≤ Real.sin b) (hδη : δ ≤ η) (θ : Fin N → ℝ) :
    ((mixedBranchCoordinates b δ θ).card : ℝ) ≤
      actualUpperPopulation η θ + actualLowerPopulation η θ := by
  have hpoint (i : Fin N) (hi : i ∈ mixedBranchCoordinates b δ θ) :
      (1 : ℝ) ≤ upperPeriodicBump η (θ i) + lowerPeriodicBump η (θ i) := by
    rcases (Finset.mem_filter.mp hi).2 with hlo | hhi
    · have h := lower_branch_plateau_window b η (θ i + b) hη hwidth (hlo.trans hδη)
      have he : -b + (θ i + b) = θ i := by ring
      rw [he] at h
      rw [h.1, h.2]
      norm_num
    · have h := upper_branch_plateau_window b η (θ i - b) hη hwidth (hhi.trans hδη)
      have he : b + (θ i - b) = θ i := by ring
      rw [he] at h
      rw [h.1, h.2]
      norm_num
  calc
    _ = ∑ _i ∈ mixedBranchCoordinates b δ θ, (1 : ℝ) := by simp
    _ ≤ ∑ i ∈ mixedBranchCoordinates b δ θ,
        (upperPeriodicBump η (θ i) + lowerPeriodicBump η (θ i)) := Finset.sum_le_sum hpoint
    _ ≤ ∑ i : Fin N, (upperPeriodicBump η (θ i) + lowerPeriodicBump η (θ i)) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun i _ _ => add_nonneg (upperPeriodicBump_bounds η (θ i)).1 (lowerPeriodicBump_bounds η (θ i)).1)
    _ = _ := by rw [Finset.sum_add_distrib]; rfl

def mixedVertexWeight {N : ℕ} (S : Finset (Fin N)) (i : Fin N) : ℝ :=
  if i ∈ S then Real.sqrt ((N : ℝ) / S.card) else 1

theorem mixedVertexWeight_ge_one {N : ℕ} (S : Finset (Fin N)) (i : Fin N) :
    1 ≤ mixedVertexWeight S i := by
  unfold mixedVertexWeight
  split_ifs with hi
  · have hc : 0 < S.card := Finset.card_pos.mpr ⟨i, hi⟩
    have hcR : (0 : ℝ) < S.card := by exact_mod_cast hc
    have hcN : (S.card : ℝ) ≤ N := by
      have hcard : S.card ≤ N := by
        simpa only [Fintype.card_fin] using Finset.card_le_univ S
      exact_mod_cast hcard
    have hratio : (1 : ℝ) ≤ (N : ℝ) / S.card := (le_div_iff₀ hcR).mpr (by simpa using hcN)
    have hroot := Real.sqrt_nonneg ((N : ℝ) / S.card)
    have hs := Real.sq_sqrt (by positivity : 0 ≤ (N : ℝ) / S.card)
    nlinarith
  · exact le_rfl

theorem mixedVertexWeight_product {N : ℕ} (S : Finset (Fin N)) :
    (∏ i, mixedVertexWeight S i) = Real.sqrt ((N : ℝ) / S.card) ^ S.card := by
  unfold mixedVertexWeight
  rw [Finset.prod_ite_mem_eq]
  simp only [Finset.prod_const]

theorem mixedVertexWeight_total_cost {N : ℕ} (S : Finset (Fin N)) :
    (∏ i, mixedVertexWeight S i) ≤ Real.exp ((N : ℝ) / 2) := by
  rw [mixedVertexWeight_product]
  by_cases hc : S.card = 0
  · simp only [hc, pow_zero]
    exact Real.one_le_exp (by positivity)
  · have hc0 : (0 : ℝ) < S.card := by exact_mod_cast Nat.pos_of_ne_zero hc
    have hN : (0 : ℝ) < N := by
      have hcard : S.card ≤ N := by
        simpa only [Fintype.card_fin] using Finset.card_le_univ S
      exact_mod_cast lt_of_lt_of_le (Nat.pos_of_ne_zero hc) hcard
    have hratio : 0 < (N : ℝ) / S.card := div_pos hN hc0
    apply (Real.log_le_iff_le_exp (pow_pos (Real.sqrt_pos.mpr hratio) _)).mp
    rw [Real.log_pow, Real.log_sqrt hratio.le]
    have hl := Real.log_le_sub_one_of_pos hratio
    have hm := mul_le_mul_of_nonneg_left hl hc0.le
    have he : (S.card : ℝ) * ((N : ℝ) / S.card) = N := by field_simp
    nlinarith

end
end IsingBulk.AnisoF002.Isotropic
