import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Data.Matrix.Basis
import Mathlib.Tactic

/-!
# Exact marked-entry expansion of determinant jets

The marks are actual matrix entry derivatives, including their signs.  No
entry is divided out, so this expansion remains valid on collision loci.
The finite index count is polynomial in the matrix size at every fixed jet
order.  This is the algebraic part of LT22's marked-minor argument; analytic
bounds for the actual transported scalar coefficients are separate.
-/

namespace IsingBulk.Preferred22
noncomputable section
open scoped BigOperators ContDiff Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false

theorem matrix_direction_entry_expansion {N : ℕ}
    (B : Matrix (Fin N) (Fin N) ℂ) :
    B = ∑ a : Fin N × Fin N, B a.1 a.2 • Matrix.single a.1 a.2 (1:ℂ) := by
  classical
  simp only [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [Fintype.sum_prod_type]
  exact Matrix.matrix_eq_sum_single B

theorem multilinear_matrix_entry_expansion {N ell : ℕ}
    (F : (Matrix (Fin N) (Fin N) ℂ) [×ell]→L[ℂ] ℂ)
    (B : Fin ell → Matrix (Fin N) (Fin N) ℂ) :
    F B = ∑ marks : Fin ell → Fin N × Fin N,
      (∏ r, B r (marks r).1 (marks r).2) *
        F (fun r => Matrix.single (marks r).1 (marks r).2 (1:ℂ)) := by
  classical
  have hB : B = fun r => ∑ a : Fin N × Fin N,
      B r a.1 a.2 • Matrix.single a.1 a.2 (1:ℂ) := by
    funext r
    exact matrix_direction_entry_expansion (B r)
  conv_lhs => rw [hB]
  change F.toMultilinearMap (fun r => ∑ a : Fin N × Fin N,
    B r a.1 a.2 • Matrix.single a.1 a.2 (1:ℂ)) = _
  rw [F.toMultilinearMap.map_sum]
  apply Finset.sum_congr rfl
  intro marks _
  convert! F.toMultilinearMap.map_smul_univ
    (fun r => B r (marks r).1 (marks r).2)
    (fun r => Matrix.single (marks r).1 (marks r).2 (1:ℂ)) using 1

/-- The actual signed determinant derivative in the selected entries. -/
def markedDeterminant {N ell : ℕ} (K : Matrix (Fin N) (Fin N) ℂ)
    (marks : Fin ell → Fin N × Fin N) : ℂ :=
  iteratedFDeriv ℂ ell Matrix.det K
    (fun r => Matrix.single (marks r).1 (marks r).2 (1:ℂ))

theorem determinant_jet_marked_expansion {N ell : ℕ}
    (K : Matrix (Fin N) (Fin N) ℂ)
    (B : Fin ell → Matrix (Fin N) (Fin N) ℂ) :
    iteratedFDeriv ℂ ell Matrix.det K B =
      ∑ marks : Fin ell → Fin N × Fin N,
        (∏ r, B r (marks r).1 (marks r).2) * markedDeterminant K marks :=
  multilinear_matrix_entry_expansion _ B

theorem marked_entry_index_card (N ell : ℕ) :
    Fintype.card (Fin ell → Fin N × Fin N) = N^(2*ell) := by
  simp [pow_mul, pow_two]

theorem determinant_contDiff (N : ℕ) :
    ContDiff ℂ ∞ (Matrix.det : Matrix (Fin N) (Fin N) ℂ → ℂ) := by
  have hentry (i j : Fin N) : ContDiff ℂ ∞
      (fun A : Matrix (Fin N) (Fin N) ℂ => A i j) :=
    contDiff_apply_apply ℂ ℂ i j
  change ContDiff ℂ ∞ (fun A : Matrix (Fin N) (Fin N) ℂ => A.det)
  simp only [Matrix.det_apply']
  apply ContDiff.sum
  intro σ _
  exact (contDiff_prod (fun j _ => hentry (σ j) j)).const_smul
    ((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ))

/-- Directions in each outer determinant slot supplied by the actual inner
kernel derivatives for an ordered partition of the differentiation labels. -/
def partitionKernelDirections {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {N k : ℕ} (K : E → Matrix (Fin N) (Fin N) ℂ) (x : E)
    (c : OrderedFinpartition k) (v : Fin k → E) :
    Fin c.length → Matrix (Fin N) (Fin N) ℂ :=
  c.applyOrderedFinpartition (fun r => iteratedFDeriv ℂ (c.partSize r) K x) v

theorem composite_determinant_jet_marked_expansion
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {N k : ℕ} (K : E → Matrix (Fin N) (Fin N) ℂ) (x : E)
    (hK : ContDiffAt ℂ ∞ K x) (v : Fin k → E) :
    iteratedFDeriv ℂ k (fun y => (K y).det) x v =
      ∑ c : OrderedFinpartition k, ∑ marks : Fin c.length → Fin N × Fin N,
        (∏ r, partitionKernelDirections K x c v r (marks r).1 (marks r).2) *
          markedDeterminant (K x) marks := by
  classical
  change iteratedFDeriv ℂ k (Matrix.det ∘ K) x v = _
  rw [iteratedFDeriv_comp (determinant_contDiff N).contDiffAt hK (by simp)]
  simp only [FormalMultilinearSeries.taylorComp, sum_apply,
    FormalMultilinearSeries.compAlongOrderedFinpartition_apply, ftaylorSeries]
  apply Finset.sum_congr rfl
  intro c _
  exact determinant_jet_marked_expansion (K x) (partitionKernelDirections K x c v)

/-- Actual index family for the exact mixed-derivative expansion. -/
abbrev MarkedJetIndex (N k : ℕ) :=
  (c : OrderedFinpartition k) × (Fin c.length → Fin N × Fin N)

theorem marked_jet_index_card_le (N k : ℕ) (hN : 1≤N) :
    Fintype.card (MarkedJetIndex N k) ≤
      Fintype.card (OrderedFinpartition k) * N^(2*k) := by
  classical
  change Fintype.card ((c : OrderedFinpartition k) × (Fin c.length → Fin N × Fin N)) ≤ _
  rw [Fintype.card_sigma]
  simp only [marked_entry_index_card]
  calc
    (∑ c : OrderedFinpartition k, N^(2*c.length)) ≤ ∑ _c : OrderedFinpartition k, N^(2*k) := by
      apply Finset.sum_le_sum
      intro c _
      exact Nat.pow_le_pow_right hN (Nat.mul_le_mul_left 2 c.length_le)
    _ = _ := by simp [Nat.mul_comm]

theorem marked_jet_order_le {N k : ℕ} (z : MarkedJetIndex N k) : z.1.length ≤ k :=
  z.1.length_le

end
end IsingBulk.Preferred22
