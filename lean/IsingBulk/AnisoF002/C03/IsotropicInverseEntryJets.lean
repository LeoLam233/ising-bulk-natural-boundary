import IsingBulk.AnisoF002.C03.IsotropicActualInverseJacobianJets

/-!
# Actual inverse entries and finite real angular differentiation

The coefficients used when transport differentiates a smooth cutoff
are entries of the full balanced inverse. They inherit the same common
neighborhood and all finite angular jet estimates as that operator.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators
open Set

def angularOperatorEntry {N : ℕ} (i j : Fin N) : AngularOperator N →L[ℝ] ℂ :=
  ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) i).comp
    (ContinuousLinearMap.apply ℂ (Fin N → ℂ) (Pi.single j 1))).restrictScalars ℝ

theorem angularOperatorEntry_apply {N : ℕ} (i j : Fin N) (L : AngularOperator N) :
    angularOperatorEntry i j L = L (Pi.single j 1) i := rfl

theorem angularOperatorEntry_norm_le {N : ℕ} (i j : Fin N) :
    ‖angularOperatorEntry i j‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro L
  rw [angularOperatorEntry_apply, one_mul]
  calc
    ‖L (Pi.single j 1) i‖ ≤ ‖L (Pi.single j 1)‖ := norm_le_pi_norm _ i
    _ ≤ ‖L‖ * ‖(Pi.single j 1 : Fin N → ℂ)‖ := L.le_opNorm _
    _ = ‖L‖ := by rw [Pi.norm_single, norm_one, mul_one]

def actualBalancedInverseEntry {N : ℕ} (η τ ξ : ℝ) (i j : Fin N)
    (θ : Fin N → ℝ) : ℂ :=
  angularOperatorEntry i j (actualBalancedInverseOperator η τ ξ θ)

theorem angularOperator_apply_eq_sum {N : ℕ} (L : AngularOperator N)
    (v : Fin N → ℂ) (i : Fin N) :
    L v i = ∑ j, angularOperatorEntry i j L * v j := by
  have hv : v = ∑ j : Fin N, v j • (Pi.single j 1 : Fin N → ℂ) := by
    ext l
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  conv_lhs => rw [hv]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    angularOperatorEntry_apply]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

theorem exists_actual_inverse_entries_all_angular_jets (η : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ k : ℕ, ∃ Ck : ℝ, 0 < Ck ∧
      ∀ (N : ℕ), 0 < N → ∀ τ ξ : ℝ, τ ∈ Icc 0 δ → ξ ∈ Icc 0 1 →
        ∀ i j : Fin N, FiniteJetControl k (actualBalancedInverseEntry η τ ξ i j)
          (Ck * (N : ℝ) ^ (3 * k)) := by
  obtain ⟨δ, hδ, hδ1, hjet⟩ := exists_actual_inverse_jacobian_all_angular_jets η
  refine ⟨δ, hδ, hδ1, ?_⟩
  intro k
  obtain ⟨Ck, hCk, hC⟩ := hjet k
  refine ⟨Ck, hCk, ?_⟩
  intro N hN τ ξ hτ hξ i j
  exact ((hC N hN τ ξ hτ hξ).clm (angularOperatorEntry i j)).mono_bound
    (mul_le_of_le_one_left (by positivity) (angularOperatorEntry_norm_le i j))

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem FiniteJetControl.mono_order {k m : ℕ} {f : E → F} {C : ℝ}
    (h : FiniteJetControl k f C) (hm : m ≤ k) : FiniteJetControl m f C :=
  ⟨h.smooth.of_le (by exact_mod_cast hm), fun j hj x => h.bound j (hj.trans hm) x⟩

theorem FiniteJetControl.scalarPartial {k : ℕ} {f : E → ℂ} {C : ℝ}
    (hf : FiniteJetControl (k + 1) f C) (v : E) (hv : ‖v‖ ≤ 1) :
    FiniteJetControl k (scalarPartial f v) C := by
  refine ⟨?_, ?_⟩
  · exact (ContinuousLinearMap.apply ℝ ℂ v).contDiff.comp
      (hf.smooth.fderiv_right (by simp))
  · intro m hm x
    have hh := norm_iteratedFDeriv_scalarPartial_le f v x m
      (hf.smooth.of_le (by exact_mod_cast (Nat.add_le_add_right hm 1))).contDiffAt
    exact hh.trans ((mul_le_of_le_one_left (norm_nonneg _) hv).trans
      (hf.bound (m + 1) (Nat.add_le_add_right hm 1) x))

end IsingBulk.AnisoF002.Isotropic
