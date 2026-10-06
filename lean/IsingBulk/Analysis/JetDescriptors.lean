import Mathlib.Tactic

/-! The descriptor layer of lem:jets. Each transition records a product-rule
mechanism. This module does not identify analytic coefficients with descriptors. -/
namespace IsingBulk.Jets

structure JetDescriptor where
  pole : ℕ
  cutoff : ℕ
  parameter : ℕ
  numerator : ℕ
  deriving DecidableEq

def JetDescriptor.Valid (j : ℕ) (d : JetDescriptor) : Prop :=
  d.pole + d.cutoff + d.numerator ≤ 2*j ∧
  d.parameter + d.cutoff + d.numerator ≤ j

inductive JetAction (N : ℕ) where
  | coefficientParameter
  | coefficientSpatial (i : Fin N)
  | divergence
  | numeratorSpatial (i : Fin N)
  | numeratorParameter
  | cutoffSpatial (i : Fin N)
  deriving DecidableEq

def JetAction.apply {N : ℕ} (a : JetAction N) (d : JetDescriptor) : JetDescriptor :=
  match a with
  | .coefficientParameter => d
  | .coefficientSpatial _ => { d with pole := d.pole+2 }
  | .divergence => { d with pole := d.pole+2 }
  | .numeratorSpatial _ => { d with pole := d.pole+1, numerator := d.numerator+1 }
  | .numeratorParameter => { d with parameter := d.parameter+1 }
  | .cutoffSpatial _ => { d with pole := d.pole+1, cutoff := d.cutoff+1 }

theorem valid_action {N j : ℕ} (a : JetAction N) (d : JetDescriptor)
    (h : d.Valid j) : (a.apply d).Valid (j+1) := by
  cases a <;> simp_all [JetAction.apply, JetDescriptor.Valid] <;> omega

def actions (N : ℕ) : List (JetAction N) :=
  [.coefficientParameter, .divergence, .numeratorParameter] ++
    (List.finRange N).map JetAction.coefficientSpatial ++
    (List.finRange N).map JetAction.numeratorSpatial ++
    (List.finRange N).map JetAction.cutoffSpatial

theorem actions_length (N : ℕ) : (actions N).length = 3+3*N := by
  simp [actions]
  omega

theorem mem_actions {N : ℕ} (a : JetAction N) : a ∈ actions N := by
  cases a <;> simp [actions]

def descendants (N : ℕ) : ℕ → List JetDescriptor
  | 0 => [⟨0,0,0,0⟩]
  | j+1 => (descendants N j).flatMap (fun d => (actions N).map (fun a => a.apply d))

theorem descendants_valid (N j : ℕ) :
    ∀ d ∈ descendants N j, d.Valid j := by
  induction j with
  | zero => simp [descendants, JetDescriptor.Valid]
  | succ j ih =>
    intro d hd
    simp only [descendants, List.mem_flatMap, List.mem_map] at hd
    obtain ⟨e, he, a, _, rfl⟩ := hd
    exact valid_action a e (ih e he)

theorem descendants_length (N j : ℕ) : (descendants N j).length = (3+3*N)^j := by
  induction j with
  | zero => simp [descendants]
  | succ j ih =>
    simp [descendants, List.length_flatMap, actions_length, ih, pow_succ, mul_comm]

/-- Explicit polynomial bound: j is fixed before N; its constant is 6^j. -/
theorem descendants_polynomial_bound (j : ℕ) :
    ∀ N : ℕ, 1 ≤ N → (descendants N j).length ≤ 6^j * N^j := by
  intro N hN
  rw [descendants_length, ← mul_pow]
  exact Nat.pow_le_pow_left (by omega) j

/-- A single j-dependent integer works as both prefactor and exponent. -/
theorem descendants_source_bound (j : ℕ) :
    ∃ C : ℕ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → (descendants N j).length ≤ C * N^C := by
  refine ⟨6^j+j+1, by positivity, ?_⟩
  intro N hN
  have hC : (6:ℕ)^j ≤ 6^j+j+1 := (Nat.le_add_right _ _).trans (Nat.le_succ _)
  have hj : j ≤ (6:ℕ)^j+j+1 := (Nat.le_add_left _ _).trans (Nat.le_succ _)
  calc
    _ ≤ 6^j * N^j := descendants_polynomial_bound j N hN
    _ ≤ (6^j+j+1) * N^(6^j+j+1) :=
      Nat.mul_le_mul hC (Nat.pow_le_pow_right hN hj)

end IsingBulk.Jets
