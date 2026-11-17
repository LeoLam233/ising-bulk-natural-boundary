import IsingBulk.AnisoF002.C03.IsotropicPopulationJets
import IsingBulk.AnisoF002.C03.IsotropicRightCutoffAnchors

/-!
# The actual lower-population right and anchored weights

Every real angular jet is retained.  The full lower weight is decomposed
exactly into its right product and the named compact-anchor terms.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set Filter
open scoped Topology BigOperators

theorem actualUpperPopulation_contDiff (η : ℝ) (N : ℕ) {k : ℕ∞} :
    ContDiff ℝ k (@actualUpperPopulation N η) :=
  ContDiff.sum (fun i _ => (upperPeriodicBump_contDiff η).comp (contDiff_apply ℝ ℝ i))

theorem actualLowerPopulation_contDiff (η : ℝ) (N : ℕ) {k : ℕ∞} :
    ContDiff ℝ k (@actualLowerPopulation N η) :=
  ContDiff.sum (fun i _ => (lowerPeriodicBump_contDiff η).comp (contDiff_apply ℝ ℝ i))

theorem lowerPopulationCutoff_contDiff (η : ℝ) (N : ℕ) {k : ℕ∞} :
    ContDiff ℝ k (@lowerPopulationCutoff N η) :=
  ((contDiff_const.sub (populationTransition_contDiff.comp
    (actualUpperPopulation_contDiff η N))).mul
    (contDiff_const.add (populationTransition_contDiff.comp
      (actualLowerPopulation_contDiff η N)))).div_const 2

theorem lowerPopulationCutoff_complex_contDiff (η : ℝ) (N : ℕ) {k : ℕ∞} :
    ContDiff ℝ k (fun θ : Fin N → ℝ => (lowerPopulationCutoff η θ : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp (lowerPopulationCutoff_contDiff η N)

theorem lowerPopulationCutoff_all_jets (η : ℝ) (k : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ N : ℕ, 0 < N →
      FiniteJetControl k (fun θ : Fin N → ℝ => (lowerPopulationCutoff η θ : ℂ))
        (C * (N : ℝ) ^ (2 * k)) := by
  obtain ⟨A, hA, hjet⟩ := actual_population_transition_jets η k
  let C := (2 : ℝ) ^ k * (2 * A) * (2 * A)
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hC : 1 ≤ C := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (by linarith)) (by linarith)
  refine ⟨C, hC, ?_⟩
  intro N hN
  obtain ⟨hp, hq⟩ := hjet N hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hD : 1 ≤ A * (N : ℝ) ^ k := one_le_mul_of_one_le_of_one_le hA (one_le_pow₀ hN1)
  have hone := finiteJetControl_const (E := Fin N → ℝ) k (1 : ℂ) 1 (by simp)
  have hleft := (hone.sub hp).mono_bound (show 1 + A * (N : ℝ) ^ k ≤
    2 * (A * (N : ℝ) ^ k) by linarith)
  have hright := (hone.add hq).mono_bound (show 1 + A * (N : ℝ) ^ k ≤
    2 * (A * (N : ℝ) ^ k) by linarith)
  have hh := (hleft.mul hright (by positivity) (by positivity)).complex_mul_const ((2 : ℂ)⁻¹)
  have hhalf : ‖(2 : ℂ)⁻¹‖ ≤ 1 := by norm_num
  have hbound : ‖(2 : ℂ)⁻¹‖ * (2 ^ k * (2 * (A * (N : ℝ) ^ k)) *
      (2 * (A * (N : ℝ) ^ k))) ≤ C * (N : ℝ) ^ (2 * k) := by
    calc
      _ ≤ 1 * (2 ^ k * (2 * (A * (N : ℝ) ^ k)) * (2 * (A * (N : ℝ) ^ k))) :=
        mul_le_mul_of_nonneg_right hhalf (by positivity)
      _ = _ := by dsimp [C]; rw [pow_mul]; ring
  convert hh.mono_bound hbound using 1
  funext θ
  simp [lowerPopulationCutoff, div_eq_mul_inv]

def actualLowerRightCutoff (η b δ ρ : ℝ) (N : ℕ) (θ : Fin N → ℝ) : ℂ :=
  (lowerPopulationCutoff η θ : ℂ) * rightCutoffProduct b δ ρ N θ

def actualLowerAnchorCutoff (η b δ ρ : ℝ) {N : ℕ} (a : Fin N) (θ : Fin N → ℝ) : ℂ :=
  (lowerPopulationCutoff η θ : ℂ) * rightCutoffAnchor b δ ρ a θ

theorem actualLowerRightCutoff_contDiff (η b δ ρ : ℝ) (N : ℕ) {k : ℕ∞} :
    ContDiff ℝ k (actualLowerRightCutoff η b δ ρ N) :=
  (lowerPopulationCutoff_complex_contDiff η N).mul (rightCutoffProduct_contDiff b δ ρ N)

theorem actualLowerAnchorCutoff_contDiff (η b δ ρ : ℝ) {N : ℕ} (a : Fin N) {k : ℕ∞} :
    ContDiff ℝ k (actualLowerAnchorCutoff η b δ ρ a) :=
  (lowerPopulationCutoff_complex_contDiff η N).mul (rightCutoffAnchor_contDiff b δ ρ a)

theorem actual_lower_right_anchor_partition (η b δ ρ : ℝ) (N : ℕ) (θ : Fin N → ℝ) :
    (lowerPopulationCutoff η θ : ℂ) = actualLowerRightCutoff η b δ ρ N θ +
      ∑ a, actualLowerAnchorCutoff η b δ ρ a θ := by
  have hh := congrArg (fun z : ℂ => (lowerPopulationCutoff η θ : ℂ) * z)
    (rightCutoff_exact_partition b δ ρ N θ)
  simpa only [mul_one, mul_add, Finset.mul_sum, actualLowerRightCutoff,
    actualLowerAnchorCutoff] using hh

theorem actual_lower_right_anchor_jets (η b δ ρ : ℝ) (k : ℕ) :
    ∃ A C : ℝ, 1 ≤ A ∧ 1 ≤ C ∧ ∀ N : ℕ, 0 < N →
      FiniteJetControl k (actualLowerRightCutoff η b δ ρ N)
        (A * C ^ N * (N : ℝ) ^ (2 * k)) ∧
      ∀ a : Fin N, FiniteJetControl k (actualLowerAnchorCutoff η b δ ρ a)
        (A * C ^ N * (N : ℝ) ^ (2 * k)) := by
  obtain ⟨A, hA, hpop⟩ := lowerPopulationCutoff_all_jets η k
  obtain ⟨C, hC, hcut⟩ := exists_rightCutoff_product_anchor_jets b δ ρ k
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  refine ⟨2 ^ k * A, C, one_le_mul_of_one_le_of_one_le
    (one_le_pow₀ (by norm_num)) hA, hC, ?_⟩
  intro N hN
  constructor
  · have hh := (hpop N hN).mul (hcut N).1 (by positivity) (by positivity)
    exact hh.mono_bound (le_of_eq (by ring))
  · intro a
    have hh := (hpop N hN).mul ((hcut N).2 a) (by positivity) (by positivity)
    exact hh.mono_bound (le_of_eq (by ring))

theorem lowerPopulationCutoff_tsupport {N : ℕ} (η : ℝ) :
    tsupport (fun θ : Fin N → ℝ => (lowerPopulationCutoff η θ : ℂ)) ⊆
      {θ | actualUpperPopulation η θ ≤ 1 / 2} := by
  apply closure_minimal
  · intro θ hθ
    exact (lowerPopulationCutoff_support η θ (by
      intro hh
      exact hθ (by change (lowerPopulationCutoff η θ : ℂ) = 0; rw [hh, Complex.ofReal_zero]))).le
  · exact isClosed_le (actualUpperPopulation_contDiff η N (k := 0)).continuous continuous_const

theorem actualLowerRightCutoff_jet_population {N : ℕ} (η b δ ρ : ℝ)
    (k : ℕ) (θ : Fin N → ℝ)
    (hne : iteratedFDeriv ℝ k (actualLowerRightCutoff η b δ ρ N) θ ≠ 0) :
    actualUpperPopulation η θ ≤ 1 / 2 :=
  lowerPopulationCutoff_tsupport η (tsupport_mul_subset_left (support_iteratedFDeriv_subset k hne))

theorem actualLowerAnchorCutoff_jet_compact_left {b δ ρ η : ℝ}
    (h : RightCutoffGeometry b δ ρ) (hη : 0 < η) (hρπ : ρ ≤ Real.pi / 2)
    (hgap : 2 * η ≤ Real.sin ρ) {N : ℕ} (a : Fin N) (k : ℕ) (θ : Fin N → ℝ)
    (hθ : θ a ∈ Icc (-Real.pi - ρ) (Real.pi - ρ))
    (hne : iteratedFDeriv ℝ k (actualLowerAnchorCutoff η b δ ρ a) θ ≠ 0) :
    actualUpperPopulation η θ ≤ 1 / 2 ∧ θ a ∈ Icc (-Real.pi - ρ) (-b - δ / 2) := by
  have hs := support_iteratedFDeriv_subset k hne
  have hP := lowerPopulationCutoff_tsupport η (tsupport_mul_subset_left hs)
  have ha := rightCutoffAnchor_tsupport h a (tsupport_mul_subset_right hs)
  have hex := upper_plateau_excluded_of_small_population hη h.rho_pos hρπ hgap θ hP a
  refine ⟨hP, hθ.1, ?_⟩
  rcases ha with hl | hu
  · exact hl
  · exact (hex ⟨hu, hθ.2⟩).elim

end
end IsingBulk.AnisoF002.Isotropic
