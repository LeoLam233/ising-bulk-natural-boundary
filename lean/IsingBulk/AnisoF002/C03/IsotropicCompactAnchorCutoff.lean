import IsingBulk.AnisoF002.C03.IsotropicCompactWeightedHolomorphy

/-!
# Smooth compact lifts of the literal lower anchor weights

The window transitions occur inside the excluded upper bump plateau.
It therefore preserves the exact periodic lower-anchor weight on its
shifted fundamental interval. Every derivative retains the full
population factor, ordered anchor prefix, compact one-sided rectangle,
and named left-anchor cosine gap.
-/

noncomputable section
namespace IsingBulk.AnisoF002.Isotropic
open scoped Topology BigOperators ContDiff
open Set Filter

def compactLowerWindow (ρ θ : ℝ) : ℝ :=
  Real.smoothTransition ((θ + Real.pi + ρ) / (ρ / 2)) *
    Real.smoothTransition ((ρ - θ) / (ρ / 2))

theorem compactLowerWindow_contDiff (ρ : ℝ) {k : ℕ∞} :
    ContDiff ℝ k (compactLowerWindow ρ) :=
  (Real.smoothTransition.contDiff.comp
    (((contDiff_id.add contDiff_const).add contDiff_const).div_const _)).mul
    (Real.smoothTransition.contDiff.comp ((contDiff_const.sub contDiff_id).div_const _))

theorem compactLowerWindow_zero {ρ θ : ℝ} (hρ : 0 < ρ)
    (hθ : θ ≤ -Real.pi - ρ ∨ ρ ≤ θ) : compactLowerWindow ρ θ = 0 := by
  rcases hθ with hl | hu
  · have hz := Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (by linarith : θ + Real.pi + ρ ≤ 0) (half_pos hρ).le)
    simp only [compactLowerWindow, hz, zero_mul]
  · have hz := Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (by linarith : ρ - θ ≤ 0) (half_pos hρ).le)
    simp only [compactLowerWindow, hz, mul_zero]

theorem compactLowerWindow_one {ρ θ : ℝ} (hρ : 0 < ρ)
    (hθ : θ ∈ Icc (-Real.pi - ρ / 2) (ρ / 2)) : compactLowerWindow ρ θ = 1 := by
  have hl : Real.smoothTransition ((θ + Real.pi + ρ) / (ρ / 2)) = 1 := Real.smoothTransition.one_of_one_le
    ((one_le_div (half_pos hρ)).mpr (by linarith only [hθ.1]))
  have hu : Real.smoothTransition ((ρ - θ) / (ρ / 2)) = 1 := Real.smoothTransition.one_of_one_le
    ((one_le_div (half_pos hρ)).mpr (by linarith only [hθ.2]))
  simp only [compactLowerWindow, hl, hu, mul_one]

theorem compactLowerWindow_tsupport {ρ : ℝ} (hρ : 0 < ρ) :
    tsupport (compactLowerWindow ρ) ⊆ Icc (-Real.pi - ρ) ρ := by
  apply closure_minimal _ isClosed_Icc
  intro θ hθ
  constructor
  · by_contra hh
    exact hθ (compactLowerWindow_zero hρ (Or.inl (le_of_not_ge hh)))
  · by_contra hh
    exact hθ (compactLowerWindow_zero hρ (Or.inr (le_of_not_ge hh)))

theorem compactLowerWindow_jets {ρ : ℝ} (hρ : 0 < ρ) (k : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ FiniteJetControl k (compactLowerWindow ρ) C := by
  have hc : HasCompactSupport (compactLowerWindow ρ) :=
    isCompact_Icc.of_isClosed_subset isClosed_closure (compactLowerWindow_tsupport hρ)
  obtain ⟨C, _, hj⟩ := hc.exists_bound_iteratedFDeriv (compactLowerWindow_contDiff ρ) k
  exact ⟨max 1 C, le_max_left _ _, compactLowerWindow_contDiff ρ,
    fun j hjk θ => (hj j hjk θ).trans (le_max_right _ _)⟩

def compactLowerWindowProduct (ρ : ℝ) (N : ℕ) (θ : Fin N → ℝ) : ℂ :=
  ∏ i, (compactLowerWindow ρ (θ i) : ℂ)

def actualLowerCompactAnchorCutoff (η b δ ρ : ℝ) {N : ℕ}
    (a : Fin N) (θ : Fin N → ℝ) : ℂ :=
  actualLowerAnchorCutoff η b δ ρ a θ * compactLowerWindowProduct ρ N θ

theorem compactLowerWindowProduct_contDiff (ρ : ℝ) (N : ℕ) {k : ℕ∞} :
    ContDiff ℝ k (compactLowerWindowProduct ρ N) :=
  contDiff_prod (fun i _ => Complex.ofRealCLM.contDiff.comp
    ((compactLowerWindow_contDiff ρ).comp (contDiff_apply ℝ ℝ i)))

theorem actualLowerCompactAnchorCutoff_contDiff (η b δ ρ : ℝ) {N : ℕ}
    (a : Fin N) {k : ℕ∞} : ContDiff ℝ k (actualLowerCompactAnchorCutoff η b δ ρ a) :=
  (actualLowerAnchorCutoff_contDiff η b δ ρ a).mul (compactLowerWindowProduct_contDiff ρ N)

theorem lower_population_shifted_core {η ρ : ℝ} (hη : 0 < η) (hρ : 0 < ρ)
    (hρπ : ρ ≤ Real.pi / 2) (hgap : 2 * η ≤ Real.sin (ρ / 2))
    {N : ℕ} (θ : Fin N → ℝ) (hP : actualUpperPopulation η θ ≤ 1 / 2)
    (i : Fin N) (hi : θ i ∈ Icc (-Real.pi - ρ) (Real.pi - ρ)) :
    θ i ∈ Icc (-Real.pi - ρ / 2) (ρ / 2) := by
  have hρhalf : ρ / 2 ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have hsum := Finset.single_le_sum
    (fun j (_ : j ∈ (Finset.univ : Finset (Fin N))) => (upperPeriodicBump_bounds η (θ j)).1)
    (Finset.mem_univ i)
  constructor
  · by_contra hn
    have hp : θ i + 2 * Real.pi ∈ Icc (ρ / 2) (Real.pi - ρ / 2) :=
      ⟨by linarith [hi.1], by linarith⟩
    have hb := upperPeriodicBump_one_on_plateau hη (half_pos hρ) hρhalf hgap hp
    rw [(upperPeriodicBump_periodic η) (θ i)] at hb
    rw [hb] at hsum
    change (∑ j, upperPeriodicBump η (θ j)) ≤ 1 / 2 at hP
    linarith
  · by_contra hn
    exact upper_plateau_excluded_of_small_population hη (half_pos hρ) hρhalf hgap θ hP i
      ⟨(lt_of_not_ge hn).le, by linarith [hi.2]⟩

theorem actualLowerCompactAnchorCutoff_eq_periodic {η ρ : ℝ}
    (hη : 0 < η) (hρ : 0 < ρ) (hρπ : ρ ≤ Real.pi / 2)
    (hgap : 2 * η ≤ Real.sin (ρ / 2)) (b δ : ℝ) {N : ℕ}
    (a : Fin N) (θ : Fin N → ℝ)
    (hθ : ∀ i, θ i ∈ Icc (-Real.pi - ρ) (Real.pi - ρ)) :
    actualLowerCompactAnchorCutoff η b δ ρ a θ = actualLowerAnchorCutoff η b δ ρ a θ := by
  by_cases hz : actualLowerAnchorCutoff η b δ ρ a θ = 0
  · simp only [actualLowerCompactAnchorCutoff, hz, zero_mul]
  have hp : (lowerPopulationCutoff η θ : ℂ) ≠ 0 := (mul_ne_zero_iff.mp hz).1
  have hP := lowerPopulationCutoff_tsupport η (subset_closure hp)
  have he (i : Fin N) : compactLowerWindow ρ (θ i) = 1 :=
    compactLowerWindow_one hρ (lower_population_shifted_core hη hρ hρπ hgap θ hP i (hθ i))
  simp only [actualLowerCompactAnchorCutoff, compactLowerWindowProduct, he,
    Complex.ofReal_one, Finset.prod_const_one, mul_one]

theorem compactLowerWindowProduct_weighted_tsupport {ρ : ℝ} (hρ : 0 < ρ)
    {N : ℕ} (w : (Fin N → ℝ) → ℂ) :
    tsupport (fun θ => w θ * compactLowerWindowProduct ρ N θ) ⊆
      Icc (fun _ => -Real.pi - ρ) (fun _ => ρ) := by
  apply closure_minimal _ isClosed_Icc
  intro θ hθ
  have hp := (mul_ne_zero_iff.mp hθ).2
  have hi (i : Fin N) : compactLowerWindow ρ (θ i) ≠ 0 := by
    intro hz
    apply hp
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp only [hz, Complex.ofReal_zero]
  exact ⟨fun i => (compactLowerWindow_tsupport hρ (subset_closure (hi i))).1,
    fun i => (compactLowerWindow_tsupport hρ (subset_closure (hi i))).2⟩

theorem actualLowerCompactAnchorCutoff_jet_support {η b δ ρ : ℝ}
    (h : RightCutoffGeometry b δ ρ) (hη : 0 < η) (hρπ : ρ ≤ Real.pi / 2)
    (hgap : 2 * η ≤ Real.sin (ρ / 2)) {N : ℕ} (a : Fin N) (k : ℕ) (θ : Fin N → ℝ)
    (hne : iteratedFDeriv ℝ k (actualLowerCompactAnchorCutoff η b δ ρ a) θ ≠ 0) :
    actualUpperPopulation η θ ≤ 1 / 2 ∧
      (∀ i, θ i ∈ Icc (-Real.pi - ρ) ρ) ∧ θ a ≤ -b - δ / 2 := by
  have hs := support_iteratedFDeriv_subset k hne
  have hr := compactLowerWindowProduct_weighted_tsupport h.rho_pos
    (actualLowerAnchorCutoff η b δ ρ a) hs
  have ho := tsupport_mul_subset_left hs
  have hP := lowerPopulationCutoff_tsupport η (tsupport_mul_subset_left ho)
  have ha := rightCutoffAnchor_tsupport h a (tsupport_mul_subset_right ho)
  refine ⟨hP, fun i => ⟨hr.1 i, hr.2 i⟩, ?_⟩
  rcases ha with hl | hu
  · exact hl
  · have hu0 : θ a ≤ ρ := hr.2 a
    exact (upper_plateau_excluded_of_small_population hη (half_pos h.rho_pos)
      (by linarith [Real.pi_pos]) hgap θ hP a
      ⟨by linarith [h.rho_pos], by linarith [h.rho_pos]⟩).elim

theorem actualLowerCompactAnchorCutoff_jets {ρ : ℝ} (hρ : 0 < ρ)
    (η b δ : ℝ) (k : ℕ) :
    ∃ A C : ℝ, 1 ≤ A ∧ 1 ≤ C ∧ ∀ N : ℕ, 0 < N → ∀ a : Fin N,
      FiniteJetControl k (actualLowerCompactAnchorCutoff η b δ ρ a)
        (A * C ^ N * (N : ℝ) ^ (2 * k)) := by
  obtain ⟨A, C, hA, hC, hj⟩ := actual_lower_right_anchor_jets η b δ ρ k
  obtain ⟨L, hL, hwin⟩ := compactLowerWindow_jets hρ k
  have hA0 := zero_le_one.trans hA
  have hC0 := zero_le_one.trans hC
  have hL0 := zero_le_one.trans hL
  refine ⟨2 ^ k * A, C * (2 ^ k * L),
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) hA,
    one_le_mul_of_one_le_of_one_le hC
      (one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) hL), ?_⟩
  intro N hN a
  have hw := finiteJetControl_finsetProd (Finset.univ : Finset (Fin N)) k
    (fun i (θ : Fin N → ℝ) => (compactLowerWindow ρ (θ i) : ℂ)) hL0
    (fun i _ => finiteJetControl_complex_coordinate hwin i)
  have hw' : FiniteJetControl k (compactLowerWindowProduct ρ N) ((2 ^ k * L) ^ N) := by
    unfold compactLowerWindowProduct
    simpa only [Finset.card_univ, Fintype.card_fin] using hw
  exact (((hj N hN).2 a).mul hw' (by positivity) (by positivity)).mono_bound
    (le_of_eq (by rw [mul_pow]; ring))

end IsingBulk.AnisoF002.Isotropic
