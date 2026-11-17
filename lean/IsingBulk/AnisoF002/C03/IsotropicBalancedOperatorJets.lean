import IsingBulk.AnisoF002.C03.IsotropicBalancedMatrixJets

/-!
# The full balanced Jacobian as a controlled Banach-algebra element

The actual complex-linear matrix is represented as a bounded operator.
The finite entry expansion transfers every real angular jet with only
a polynomial dimension factor. One smallness choice then places all
particle-number Jacobians in the same inversion neighborhood.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators Matrix
open Set

abbrev AngularOperator (N : ℕ) := (Fin N → ℂ) →L[ℂ] (Fin N → ℂ)

def matrixUnitOperator {N : ℕ} (i j : Fin N) : AngularOperator N :=
  (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) j).smulRight
    (Pi.single i 1 : Fin N → ℂ)

theorem matrixUnitOperator_apply {N : ℕ} (i j : Fin N) (v : Fin N → ℂ) (l : Fin N) :
    matrixUnitOperator i j v l = v j * (Pi.single i 1 : Fin N → ℂ) l := rfl

theorem matrixUnitOperator_norm_le {N : ℕ} (i j : Fin N) : ‖matrixUnitOperator i j‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  change ‖v j • (Pi.single i 1 : Fin N → ℂ)‖ ≤ 1 * ‖v‖
  rw [norm_smul, Pi.norm_single, norm_one, mul_one, one_mul]
  exact norm_le_pi_norm v j

def matrixCoefficientOperator {N : ℕ} (i j : Fin N) : ℂ →L[ℝ] AngularOperator N :=
  (ContinuousLinearMap.id ℝ ℂ).smulRight (matrixUnitOperator i j)

theorem matrixCoefficientOperator_norm_le {N : ℕ} (i j : Fin N) :
    ‖matrixCoefficientOperator i j‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro a
  change ‖a • matrixUnitOperator i j‖ ≤ 1 * ‖a‖
  rw [norm_smul, one_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (matrixUnitOperator_norm_le i j)

def actualBalancedOperator {N : ℕ} (η τ ξ : ℝ) (θ : Fin N → ℝ) : AngularOperator N :=
  (actualBalancedJacobian η τ ξ θ).toContinuousLinearMap

theorem actualBalancedOperator_apply {N : ℕ} (η τ ξ : ℝ) (θ : Fin N → ℝ) (v : Fin N → ℂ) :
    actualBalancedOperator η τ ξ θ v = actualBalancedJacobian η τ ξ θ v := rfl

theorem actualBalancedOperator_entry_sum {N : ℕ} (η τ ξ : ℝ) (θ : Fin N → ℝ) :
    actualBalancedOperator η τ ξ θ =
      ∑ i, ∑ j, matrixCoefficientOperator i j (actualBalancedMatrix η τ ξ θ i j) := by
  ext v l
  rw [actualBalancedOperator_apply]
  rw [← LinearMap.toMatrix'_mulVec (actualBalancedJacobian η τ ξ θ) v]
  change (actualBalancedMatrix η τ ξ θ *ᵥ v) l = _
  simp only [sum_apply, matrixCoefficientOperator,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply,
    smul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    matrixUnitOperator_apply, Matrix.mulVec, dotProduct]
  rw [Finset.sum_comm]
  simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]

theorem exists_actual_balanced_operator_jet_control (η : ℝ) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 0 < N →
      ∀ τ ξ : ℝ, τ ∈ Icc 0 1 → ξ ∈ Icc 0 1 →
        FiniteJetControl k (actualBalancedOperator (N := N) η τ ξ) (C * (N : ℝ) ^ 3) := by
  obtain ⟨C, hC, hentries⟩ := exists_actual_balanced_matrix_jet_control η k
  refine ⟨C, hC, ?_⟩
  intro N hN τ ξ hτ hξ
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have he (i j : Fin N) : FiniteJetControl k
      (fun θ : Fin N → ℝ => matrixCoefficientOperator i j (actualBalancedMatrix η τ ξ θ i j))
      (C * N) := by
    have hh := (hentries N hN τ ξ hτ hξ i j).clm (matrixCoefficientOperator i j)
    exact hh.mono_bound (mul_le_of_le_one_left (by positivity) (matrixCoefficientOperator_norm_le i j))
  have hrow (i : Fin N) : FiniteJetControl k
      (fun θ : Fin N → ℝ => ∑ j, matrixCoefficientOperator i j (actualBalancedMatrix η τ ξ θ i j))
      ((N : ℝ) * (C * N)) := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
      finiteJetControl_finsetSum Finset.univ k _ (fun _ => C * N) (fun j _ => he i j)
  have hall := finiteJetControl_finsetSum Finset.univ k
    (fun i θ => ∑ j, matrixCoefficientOperator i j (actualBalancedMatrix η τ ξ θ i j))
    (fun _ => (N : ℝ) * (C * N)) (fun i _ => hrow i)
  have hsum : (∑ _i : Fin N, (N : ℝ) * (C * N)) = C * (N : ℝ) ^ 3 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [hsum] at hall
  have heq : actualBalancedOperator (N := N) η τ ξ =
      (fun θ => ∑ i, ∑ j, matrixCoefficientOperator i j (actualBalancedMatrix η τ ξ θ i j)) :=
    funext (actualBalancedOperator_entry_sum η τ ξ)
  rw [heq]
  exact hall

theorem exists_actual_balanced_operator_near_one (η : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ (N : ℕ), 0 < N →
      ∀ τ ξ : ℝ, τ ∈ Icc 0 δ → ξ ∈ Icc 0 1 → ∀ θ : Fin N → ℝ,
        ‖actualBalancedOperator η τ ξ θ - 1‖ ≤ (1 / 2 : ℝ) := by
  obtain ⟨L, hL, hp, hm, _, _⟩ := actual_bump_global_first_bounds η
  let δ := min 1 (1 / (8 * L))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδL : δ * (8 * L) ≤ 1 :=
    (le_div_iff₀ (show 0 < 8 * L by positivity)).mp (min_le_right _ _)
  refine ⟨δ, hδ, hδ1, ?_⟩
  intro N hN τ ξ hτ hξ θ
  have hξτ : 0 ≤ ξ * τ := mul_nonneg hξ.1 hτ.1
  have hτδ : ξ * τ ≤ δ := (mul_le_of_le_one_left hτ.1 hξ.2).trans hτ.2
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num : (0 : ℝ) ≤ 1 / 2)
  intro v
  change ‖actualBalancedJacobian η τ ξ θ v - v‖ ≤ (1 / 2 : ℝ) * ‖v‖
  have hh := balancedAngularJacobian_sub_id_bound
    (fun i => upperPeriodicBump η (θ i)) (fun i => lowerPeriodicBump η (θ i))
    (fun i => deriv (upperPeriodicBump η) (θ i)) (fun i => deriv (lowerPeriodicBump η) (θ i))
    v (ξ * τ) L (by simpa only [Fintype.card_fin] using hN) hξτ hL.le
    (fun i => upperPeriodicBump_bounds η (θ i)) (fun i => lowerPeriodicBump_bounds η (θ i))
    (fun i => hp (θ i)) (fun i => hm (θ i))
  exact hh.trans (mul_le_mul_of_nonneg_right (by nlinarith only [hδL, hτδ, hL]) (norm_nonneg _))

end IsingBulk.AnisoF002.Isotropic
