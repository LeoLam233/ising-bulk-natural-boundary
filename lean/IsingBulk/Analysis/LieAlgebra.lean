import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic

/-!
Algebraic part of rc4 lem:lie, manuscript lines 2186–2210.
This does not assert differentiation under a torus integral or Stokes' theorem
at punctures. The derivation is an operator on whole parameter-dependent
coefficients, so iteration does not freeze the vector-field coefficients.
-/
namespace IsingBulk.Lie
noncomputable section

variable {F : Type*} [Field F] [Algebra ℚ F]

/-- Algebraic model of ∂s - Lie_V on a top-form coefficient:
D is the transport derivation and c is div V. -/
def densityOperator (D : Derivation ℚ F F) (c : F) (a : F) : F := D a - c*a

theorem densityOperator_mul_frozen (D : Derivation ℚ F F) (c k a : F) (hk : D k = 0) :
    densityOperator D c (k*a) = k * densityOperator D c a := by
  simp only [densityOperator, D.leibniz, hk, smul_eq_mul, mul_zero, add_zero]
  ring

theorem iterate_densityOperator_mul_frozen (D : Derivation ℚ F F) (c k a : F)
    (hk : D k = 0) (j : ℕ) :
    (densityOperator D c)^[j] (k*a) = k * (densityOperator D c)^[j] a := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
      densityOperator_mul_frozen D c k _ hk]

/-- Nonzero simple kernel factors stay factored at every derivative order.
The nonzero hypotheses give the intended rational-function meaning. -/
theorem simple_kernel_iterate (D : Derivation ℚ F F) (c Y Z a : F)
    (hY : D Y = 0) (hZ : D Z = 0) (hY1 : 1-Y ≠ 0) (hZ1 : 1-Z ≠ 0) :
    (1-Y)⁻¹ * (1-Z)⁻¹ ≠ 0 ∧
    ∀ j : ℕ, (densityOperator D c)^[j] (((1-Y)⁻¹ * (1-Z)⁻¹)*a) =
      ((1-Y)⁻¹ * (1-Z)⁻¹) * (densityOperator D c)^[j] a := by
  refine ⟨mul_ne_zero (inv_ne_zero hY1) (inv_ne_zero hZ1), ?_⟩
  have hk : D ((1-Y)⁻¹ * (1-Z)⁻¹) = 0 := by
    simp [D.leibniz, D.leibniz_inv, hY, hZ]
  exact fun j => iterate_densityOperator_mul_frozen D c _ a hk j

/-- Iteration after each analytic first-derivative/zero-flux identity has
been proved. These stage identities are explicit inputs, not flux axioms. -/
theorem iterate_integral_of_stage_identities {A B : Type*} (D : A → A) (δ : B → B)
    (I : A → B) (a : A) (j : ℕ)
    (h : ∀ k : ℕ, k < j → I (D (D^[k] a)) = δ (I (D^[k] a))) :
    I (D^[j] a) = δ^[j] (I a) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', h j (by omega),
      ih (fun k hk => h k (by omega)), Function.iterate_succ_apply']

end
end IsingBulk.Lie
