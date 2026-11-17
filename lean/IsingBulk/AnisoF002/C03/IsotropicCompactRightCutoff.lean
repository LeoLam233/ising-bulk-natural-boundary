import IsingBulk.AnisoF002.C03.IsotropicPopulationCutoffJets
import IsingBulk.AnisoF002.C03.IsotropicRightCutoffProductSupport

/-!
# The compact lift of the actual periodic right cutoff

The compact function agrees exactly with the already constructed
periodic cutoff on the full fundamental interval.  It is zero outside
that interval and is globally smooth, so each constrained integer lift
has vanishing outer boundary currents without a diameter cutoff.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set Filter
open scoped Topology BigOperators ContDiff

def rightCutoffWindowMargin (b δ ρ : ℝ) : ℝ :=
  min (Real.pi - (b + δ)) (Real.pi - (ρ + δ / 2)) / 2

def compactRightCutoff (b δ ρ θ : ℝ) : ℝ :=
  periodicRightCutoff b δ ρ θ *
    Real.smoothTransition ((θ + Real.pi) / rightCutoffWindowMargin b δ ρ) *
    Real.smoothTransition ((Real.pi - θ) / rightCutoffWindowMargin b δ ρ)

theorem rightCutoffWindowMargin_pos {b δ ρ : ℝ} (h : RightCutoffGeometry b δ ρ) :
    0 < rightCutoffWindowMargin b δ ρ := by
  unfold rightCutoffWindowMargin
  exact half_pos (lt_min (sub_pos.mpr h.left_gap) (sub_pos.mpr h.right_gap))

theorem compactRightCutoff_contDiff (b δ ρ : ℝ) {k : ℕ∞} :
    ContDiff ℝ k (compactRightCutoff b δ ρ) :=
  ((periodicRightCutoff_contDiff b δ ρ).mul
    (Real.smoothTransition.contDiff.comp ((contDiff_id.add contDiff_const).div_const _))).mul
    (Real.smoothTransition.contDiff.comp ((contDiff_const.sub contDiff_id).div_const _))

theorem compactRightCutoff_zero_outside {b δ ρ θ : ℝ} (h : RightCutoffGeometry b δ ρ)
    (hθ : θ ≤ -Real.pi ∨ Real.pi ≤ θ) : compactRightCutoff b δ ρ θ = 0 := by
  have hm := (rightCutoffWindowMargin_pos h).le
  rcases hθ with hl | hu
  · have hz : Real.smoothTransition ((θ + Real.pi) / rightCutoffWindowMargin b δ ρ) = 0 :=
      Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hm)
    simp only [compactRightCutoff, hz, mul_zero, zero_mul]
  · have hz : Real.smoothTransition ((Real.pi - θ) / rightCutoffWindowMargin b δ ρ) = 0 :=
      Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hm)
    simp only [compactRightCutoff, hz, mul_zero]

theorem compactRightCutoff_eq_periodic {b δ ρ θ : ℝ} (h : RightCutoffGeometry b δ ρ)
    (hθ : θ ∈ Icc (-Real.pi) Real.pi) :
    compactRightCutoff b δ ρ θ = periodicRightCutoff b δ ρ θ := by
  by_cases hz : periodicRightCutoff b δ ρ θ = 0
  · simp only [compactRightCutoff, hz, zero_mul]
  have hs := periodicRightCutoff_support h hθ hz
  have hm := rightCutoffWindowMargin_pos h
  have hmL : rightCutoffWindowMargin b δ ρ ≤ Real.pi - (b + δ) := by
    have hmin := min_le_left (Real.pi - (b + δ)) (Real.pi - (ρ + δ / 2))
    have hp := sub_pos.mpr h.left_gap
    dsimp [rightCutoffWindowMargin]
    linarith
  have hmU : rightCutoffWindowMargin b δ ρ ≤ Real.pi - (ρ + δ / 2) := by
    have hmin := min_le_right (Real.pi - (b + δ)) (Real.pi - (ρ + δ / 2))
    have hp := sub_pos.mpr h.right_gap
    dsimp [rightCutoffWindowMargin]
    linarith
  have hL : Real.smoothTransition ((θ + Real.pi) / rightCutoffWindowMargin b δ ρ) = 1 :=
    Real.smoothTransition.one_of_one_le ((one_le_div hm).mpr (by linarith only [hmL, hs.1]))
  have hU : Real.smoothTransition ((Real.pi - θ) / rightCutoffWindowMargin b δ ρ) = 1 :=
    Real.smoothTransition.one_of_one_le ((one_le_div hm).mpr (by linarith only [hmU, hs.2]))
  simp only [compactRightCutoff, hL, hU, mul_one]

theorem compactRightCutoff_tsupport {b δ ρ : ℝ} (h : RightCutoffGeometry b δ ρ) :
    tsupport (compactRightCutoff b δ ρ) ⊆ Icc (-b - δ) (ρ + δ / 2) := by
  apply closure_minimal _ isClosed_Icc
  intro θ hθ
  have hfund : θ ∈ Icc (-Real.pi) Real.pi := by
    constructor
    · by_contra hh
      exact hθ (compactRightCutoff_zero_outside h (Or.inl (le_of_not_ge hh)))
    · by_contra hh
      exact hθ (compactRightCutoff_zero_outside h (Or.inr (le_of_not_ge hh)))
  have hp : periodicRightCutoff b δ ρ θ ≠ 0 := by
    rw [← compactRightCutoff_eq_periodic h hfund]
    exact hθ
  exact Ioo_subset_Icc_self (periodicRightCutoff_support h hfund hp)

theorem compactRightCutoff_hasCompactSupport {b δ ρ : ℝ} (h : RightCutoffGeometry b δ ρ) :
    HasCompactSupport (compactRightCutoff b δ ρ) :=
  isCompact_Icc.of_isClosed_subset isClosed_closure (compactRightCutoff_tsupport h)

theorem compactRightCutoff_jets {b δ ρ : ℝ} (h : RightCutoffGeometry b δ ρ) (k : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ FiniteJetControl k (compactRightCutoff b δ ρ) C := by
  obtain ⟨C, _, hC⟩ := (compactRightCutoff_hasCompactSupport h).exists_bound_iteratedFDeriv
    (compactRightCutoff_contDiff b δ ρ) k
  exact ⟨max 1 C, le_max_left _ _, compactRightCutoff_contDiff b δ ρ,
    fun m hm θ => (hC m hm θ).trans (le_max_right _ _)⟩

def compactRightProduct (b δ ρ : ℝ) (N : ℕ) (θ : Fin N → ℝ) : ℂ :=
  ∏ i, (compactRightCutoff b δ ρ (θ i) : ℂ)

def actualLowerCompactRightCutoff (η b δ ρ : ℝ) (N : ℕ) (θ : Fin N → ℝ) : ℂ :=
  (lowerPopulationCutoff η θ : ℂ) * compactRightProduct b δ ρ N θ

theorem compactRightProduct_contDiff (b δ ρ : ℝ) (N : ℕ) {k : ℕ∞} :
    ContDiff ℝ k (compactRightProduct b δ ρ N) :=
  contDiff_prod (fun i _ => Complex.ofRealCLM.contDiff.comp
    ((compactRightCutoff_contDiff b δ ρ).comp (contDiff_apply ℝ ℝ i)))

theorem actualLowerCompactRightCutoff_contDiff (η b δ ρ : ℝ) (N : ℕ) {k : ℕ∞} :
    ContDiff ℝ k (actualLowerCompactRightCutoff η b δ ρ N) :=
  (lowerPopulationCutoff_complex_contDiff η N).mul (compactRightProduct_contDiff b δ ρ N)

theorem actualLowerCompactRightCutoff_eq_periodic {b δ ρ : ℝ} (h : RightCutoffGeometry b δ ρ)
    (η : ℝ) (N : ℕ) (θ : Fin N → ℝ) (hθ : ∀ i, θ i ∈ Icc (-Real.pi) Real.pi) :
    actualLowerCompactRightCutoff η b δ ρ N θ = actualLowerRightCutoff η b δ ρ N θ := by
  unfold actualLowerCompactRightCutoff actualLowerRightCutoff compactRightProduct rightCutoffProduct
  simp_rw [compactRightCutoff_eq_periodic h (hθ _)]

theorem compactRightProduct_jets {b δ ρ : ℝ} (h : RightCutoffGeometry b δ ρ) (k : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ N : ℕ,
      FiniteJetControl k (compactRightProduct b δ ρ N) (C ^ N) := by
  obtain ⟨L, hL, hjet⟩ := compactRightCutoff_jets h k
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  refine ⟨2 ^ k * L, one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) hL, ?_⟩
  intro N
  have hh := finiteJetControl_finsetProd (Finset.univ : Finset (Fin N)) k
    (fun i (θ : Fin N → ℝ) => (compactRightCutoff b δ ρ (θ i) : ℂ)) hL0
    (fun i _ => finiteJetControl_complex_coordinate hjet i)
  change FiniteJetControl k (fun θ : Fin N → ℝ => ∏ i, (compactRightCutoff b δ ρ (θ i) : ℂ)) _
  simpa only [Finset.card_univ, Fintype.card_fin] using hh

theorem actualLowerCompactRightCutoff_jets {b δ ρ : ℝ} (h : RightCutoffGeometry b δ ρ)
    (η : ℝ) (k : ℕ) :
    ∃ A C : ℝ, 1 ≤ A ∧ 1 ≤ C ∧ ∀ N : ℕ, 0 < N →
      FiniteJetControl k (actualLowerCompactRightCutoff η b δ ρ N)
        (A * C ^ N * (N : ℝ) ^ (2 * k)) := by
  obtain ⟨A, hA, hpop⟩ := lowerPopulationCutoff_all_jets η k
  obtain ⟨C, hC, hcut⟩ := compactRightProduct_jets h k
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  refine ⟨2 ^ k * A, C, one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) hA, hC, ?_⟩
  intro N hN
  exact ((hpop N hN).mul (hcut N) (by positivity) (by positivity)).mono_bound (le_of_eq (by ring))

theorem compactRightProduct_weighted_tsupport {b δ ρ : ℝ} (h : RightCutoffGeometry b δ ρ)
    {N : ℕ} (w : (Fin N → ℝ) → ℂ) :
    tsupport (fun θ => w θ * compactRightProduct b δ ρ N θ) ⊆
      {θ : Fin N → ℝ | ∀ i, θ i ∈ Icc (-b - δ) (ρ + δ / 2)} := by
  apply closure_minimal
  · intro θ hθ i
    have hp : compactRightProduct b δ ρ N θ ≠ 0 := (mul_ne_zero_iff.mp hθ).2
    have hi : compactRightCutoff b δ ρ (θ i) ≠ 0 := by
      intro hz
      apply hp
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp only [hz, Complex.ofReal_zero]
    exact compactRightCutoff_tsupport h (subset_closure hi)
  · have he : {θ : Fin N → ℝ | ∀ i, θ i ∈ Icc (-b - δ) (ρ + δ / 2)} =
        ⋂ i : Fin N, (fun θ : Fin N → ℝ => θ i) ⁻¹' Icc (-b - δ) (ρ + δ / 2) := by
      ext θ
      simp only [mem_ofPred_eq, mem_iInter, mem_preimage]
    rw [he]
    exact isClosed_iInter (fun i => isClosed_Icc.preimage (continuous_apply i))

theorem compactRightProduct_weighted_all_jet_support {b δ ρ : ℝ} (h : RightCutoffGeometry b δ ρ)
    {N : ℕ} (w : (Fin N → ℝ) → ℂ) (k : ℕ) (θ : Fin N → ℝ)
    (hne : iteratedFDeriv ℝ k (fun x => w x * compactRightProduct b δ ρ N x) θ ≠ 0) :
    ∀ i, θ i ∈ Icc (-b - δ) (ρ + δ / 2) :=
  compactRightProduct_weighted_tsupport h w (support_iteratedFDeriv_subset k hne)

end
end IsingBulk.AnisoF002.Isotropic
