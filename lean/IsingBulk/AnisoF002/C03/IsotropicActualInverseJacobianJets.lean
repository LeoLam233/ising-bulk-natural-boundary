import IsingBulk.AnisoF002.C03.IsotropicBalancedOperatorJets
import IsingBulk.AnisoF002.C03.IsotropicInverseFiniteJetControl

/-!
# All real angular jets of the actual full inverse Jacobian

One smallness choice precedes every particle number and every derivative
order. At each fixed order the complete inverse has polynomial dimension
growth. The actual smooth periodic bump populations are differentiated
in full, and no inverse one-body coordinate slope occurs.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators
open Set

def actualBalancedInverseOperator {N : ℕ} (η τ ξ : ℝ) (θ : Fin N → ℝ) : AngularOperator N :=
  Ring.inverse (actualBalancedOperator η τ ξ θ)

theorem exists_actual_inverse_jacobian_all_angular_jets (η : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ k : ℕ, ∃ Ck : ℝ, 0 < Ck ∧
      ∀ (N : ℕ), 0 < N → ∀ τ ξ : ℝ, τ ∈ Icc 0 δ → ξ ∈ Icc 0 1 →
        FiniteJetControl k (actualBalancedInverseOperator (N := N) η τ ξ)
          (Ck * (N : ℝ) ^ (3 * k)) := by
  obtain ⟨δ, hδ, hδ1, hnear⟩ := exists_actual_balanced_operator_near_one η
  refine ⟨δ, hδ, hδ1, ?_⟩
  intro k
  obtain ⟨CM, hCM, hM⟩ := exists_actual_balanced_operator_jet_control η k
  let C := max 1 CM
  have hC1 : 1 ≤ C := le_max_left _ _
  have hC : 0 < C := zero_lt_one.trans_le hC1
  have hCMC : CM ≤ C := le_max_right _ _
  refine ⟨inverseFiniteJetConstant k * C ^ k,
    mul_pos (inverseFiniteJetConstant_pos k) (pow_pos hC k), ?_⟩
  intro N hN τ ξ hτ hξ
  let : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpow : (1 : ℝ) ≤ (N : ℝ) ^ 3 := one_le_pow₀ hN1
  have hCN1 : 1 ≤ C * (N : ℝ) ^ 3 :=
    hNpow.trans (le_mul_of_one_le_left (by positivity) hC1)
  have hbase : FiniteJetControl k (actualBalancedOperator (N := N) η τ ξ) (C * (N : ℝ) ^ 3) :=
    (hM N hN τ ξ ⟨hτ.1, hτ.2.trans hδ1⟩ hξ).mono_bound
      (mul_le_mul_of_nonneg_right hCMC (by positivity))
  have hinv := hbase.banach_inverse hCN1 (fun θ => hnear N hN τ ξ hτ hξ θ)
  change FiniteJetControl k (fun θ => Ring.inverse (actualBalancedOperator η τ ξ θ)) _
  convert hinv using 1
  rw [mul_pow, ← pow_mul]
  ring

theorem actualBalancedOperator_inverse_identity {N : ℕ} (η τ ξ : ℝ) (θ : Fin N → ℝ)
    (hnear : ‖actualBalancedOperator η τ ξ θ - 1‖ ≤ (1 / 2 : ℝ)) :
    actualBalancedOperator η τ ξ θ * actualBalancedInverseOperator η τ ξ θ = 1 ∧
      actualBalancedInverseOperator η τ ξ θ * actualBalancedOperator η τ ξ θ = 1 := by
  have hu : IsUnit (actualBalancedOperator η τ ξ θ) := by
    have hh : ‖1 - actualBalancedOperator η τ ξ θ‖ < 1 := by
      rw [norm_sub_rev]
      linarith only [hnear]
    simpa only [sub_sub_cancel] using isUnit_one_sub_of_norm_lt_one hh
  exact ⟨Ring.mul_inverse_cancel _ hu, Ring.inverse_mul_cancel _ hu⟩

end IsingBulk.AnisoF002.Isotropic
