import IsingBulk.AnisoF002.C03.IsotropicRightGaussian
import IsingBulk.AnisoF002.C03.IsotropicRetainedCellBound

/-!
# Uniform Gaussian bound with every retained collision coefficient

The common cells and neighborhood are constructed for the actual complete
pair before N and before the retained set. Replacing a selected pair by
its proved analytic collision coefficient costs only M per selected pair.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators
open Filter Set Metric

/-- All complete unretained pairs contribute to the Gaussian decay. The
retained collision quotient is analytic by `IsotropicRetainedPairs`. -/
theorem exists_actual_right_retainedPair_gaussian (S : ℝ) (hS : 0 < S ∧ S < 2) :
    ∃ r κ M : ℝ, 0 < r ∧ 0 < κ ∧ 0 < M ∧
      ∀ (N : ℕ) (R : Finset (Fin N × Fin N)), R ⊆ indexPairs N →
      ∀ (s : ℂ) (v : Fin N → ℂ),
        dist s (S : ℂ) < r →
        (∀ i, v i ∈ thickening r (rightCoordinateInterval S)) →
        ‖retainedInversePairProduct R (s, v)‖ ≤
          M ^ R.card * Real.exp (-κ * (N : ℝ) ^ 2 + (1 / 2 : ℝ) * N) := by
  classical
  obtain ⟨rA, hrA, _, _, hA, hfactor, _⟩ :=
    exists_right_completePair_protected_neighborhood S hS
  obtain ⟨C₀, hC₀⟩ := (rightPairParameterSegment_isCompact S).cthickening.exists_bound_of_continuousOn
    hA.continuousOn
  let C : ℝ := max 1 C₀
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hC : ∀ q ∈ cthickening rA (rightPairParameterSegment S),
      ‖inversePairCollisionCoefficient explicitRightInverse q‖ ≤ C :=
    fun q hq => (hC₀ q hq).trans (le_max_right _ _)
  let δ : ℝ := min 1 (Real.exp (-1) / (2 * C))
  have hδ : 0 < δ := lt_min zero_lt_one (div_pos (Real.exp_pos _) (by positivity))
  have hδsq : δ ^ 2 * C ≤ Real.exp (-1) := by
    have h₁ : δ ≤ 1 := min_le_left _ _
    have h₂ : δ * (2 * C) ≤ Real.exp (-1) :=
      (le_div_iff₀ (show 0 < 2 * C by positivity)).mp (min_le_right _ _)
    have h₃ := mul_le_mul_of_nonneg_right h₁ (mul_nonneg hδ.le hCpos.le)
    nlinarith [Real.exp_pos (-1)]
  obtain ⟨t, ht⟩ := (rightCoordinateInterval_isCompact S).elim_finite_subcover
    (fun a : ℂ => ball a (δ / 2)) (fun _ => isOpen_ball)
    (fun x _ => mem_iUnion.mpr ⟨x, by simp [half_pos hδ]⟩)
  have htne : t.Nonempty := by
    have h := ht (zero_mem_rightCoordinateInterval S)
    simp only [mem_iUnion] at h
    obtain ⟨a, ha, _⟩ := h
    exact ⟨a, ha⟩
  have hK : 0 < t.card := Finset.card_pos.mpr htne
  let b : ℝ := 1 / (2 * t.card)
  have hKr : (0 : ℝ) < t.card := by exact_mod_cast hK
  have hb : 0 < b := by dsimp [b]; positivity
  obtain ⟨rB, hrB, hB⟩ := exists_rightPair_small_exponential_neighborhood S b hS hb
  obtain ⟨rT, hrT, hT⟩ := (rightCoordinateInterval_isCompact S).exists_cthickening_subset_open
    (isOpen_biUnion fun a _ => isOpen_ball) ht
  let r := min rA (min rB rT)
  have hr : 0 < r := lt_min hrA (lt_min hrB hrT)
  have hrA' : r ≤ rA := min_le_left _ _
  have hrB' : r ≤ rB := (min_le_right _ _).trans (min_le_left _ _)
  have hrT' : r ≤ rT := (min_le_right _ _).trans (min_le_right _ _)
  let κ : ℝ := (1 + b - t.card * b) / (2 * t.card)
  have hmul : (t.card : ℝ) * b = 1 / 2 := by
    dsimp [b]
    field_simp
  have hκ : 0 < κ := by
    dsimp only [κ]
    apply div_pos
    · rw [hmul]
      linarith
    · positivity
  refine ⟨r, κ, C / Real.exp (-1), hr, hκ, div_pos hCpos (Real.exp_pos _), ?_⟩
  intro N R hR s v hs hv
  have hpairA : ∀ i j, (s, v i, v j) ∈ cthickening rA (rightPairParameterSegment S) := by
    intro i j
    exact thickening_subset_cthickening_of_le hrA' _ (rightPair_of_thickening hs (hv i) (hv j))
  have hpairB : ∀ i j, (s, v i, v j) ∈ cthickening rB (rightPairParameterSegment S) := by
    intro i j
    exact thickening_subset_cthickening_of_le hrB' _ (rightPair_of_thickening hs (hv i) (hv j))
  have hcover : ∀ i, ∃ a ∈ t, v i ∈ ball a (δ / 2) := by
    intro i
    have h := hT (thickening_subset_cthickening_of_le hrT' _ (hv i))
    simp only [mem_iUnion, Finset.mem_coe] at h
    obtain ⟨a, ha, hva⟩ := h
    exact ⟨a, ha, hva⟩
  choose center hcenter hdist using hcover
  let c : Fin N → Fin t.card := fun i => t.equivFin ⟨center i, hcenter i⟩
  have hwithin : ∀ i j, i < j → c i = c j →
      ‖inversePairFilled explicitRightInverse (s, v i, v j)‖ ≤ Real.exp (-1) := by
    intro i j _ hc
    have hcentereq : center i = center j :=
      congrArg Subtype.val (t.equivFin.injective hc)
    have hd : ‖v i - v j‖ ≤ δ := by
      have h₁ := hdist i
      have h₂ := hdist j
      rw [mem_ball] at h₁ h₂
      rw [← hcentereq] at h₂
      rw [← dist_eq_norm]
      exact (dist_triangle_right _ _ (center i)).trans (by linarith)
    rw [hfactor _ (hpairA i j), norm_mul, norm_pow]
    calc
      _ ≤ δ ^ 2 * C := mul_le_mul
        ((sq_le_sq₀ (norm_nonneg _) hδ.le).mpr hd) (hC _ (hpairA i j))
        (norm_nonneg _) (sq_nonneg δ)
      _ ≤ Real.exp (-1) := hδsq
  simpa only [retainedInversePairProduct, κ, neg_div] using retained_cell_product_bound c
    (fun i j => inversePairFilled explicitRightInverse (s, v i, v j))
    (fun i j => inversePairCollisionCoefficient explicitRightInverse (s, v i, v j))
    R hR 1 b C hK zero_le_one hb.le hCpos hwithin
    (fun i j _ => hB _ (hpairB i j)) (fun ij _ => hC _ (hpairA ij.1 ij.2))

end IsingBulk.AnisoF002.Isotropic
