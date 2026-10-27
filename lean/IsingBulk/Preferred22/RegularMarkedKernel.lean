import IsingBulk.Preferred22.MarkedMinorNormalization
import IsingBulk.Preferred22.Transport

/-!
# Marked derivatives of the manuscript's actual regular kernel

This file identifies the algebraic minors with `preferredMarkedMinor` and
specializes the exact mixed-derivative expansion to the literal source kernel.
The displayed analyticity hypotheses are local and explicit: this file does
not assert an analytic extension of a totalized quotient across its zero
denominator.  The global extension and transported scalar bounds remain
separate obligations in the source dependency graph.
-/
namespace IsingBulk.Preferred22
noncomputable section
open scoped BigOperators ContDiff Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false

theorem preferredMarkedMinor_ofFn {N ell : ℕ}
    (K : Matrix (Fin N) (Fin N) ℂ) (marks : Fin ell → Fin N × Fin N) :
    preferredMarkedMinor K (List.ofFn marks) = markedDeterminant K marks := by
  have he : (⟨(List.ofFn marks).length, (List.ofFn marks).get⟩ :
      (n : ℕ) × (Fin n → Fin N × Fin N)) = ⟨ell,marks⟩ :=
    (List.equivSigmaTuple (α := Fin N × Fin N)).apply_symm_apply ⟨ell,marks⟩
  exact congrArg (fun z : (n : ℕ) × (Fin n → Fin N × Fin N) =>
    markedDeterminant K z.2) he

theorem preferredMarkedMinor_hadamard {N : ℕ} (hN : 0<N)
    (K : Matrix (Fin N) (Fin N) ℂ) (marks : List (Fin N × Fin N))
    (a : ℝ) (ha : 0<a) (hK : ∀ i j, ‖K i j‖ ≤ a) :
    ‖preferredMarkedMinor K marks‖ ≤ (Real.sqrt N)^N*a^(N-marks.length) :=
  markedDeterminant_hadamard hN K (fun r => marks.get r) a ha hK

theorem preferredMarkedMinor_factorial_bound {N : ℕ} (hN : 0<N)
    (K : Matrix (Fin N) (Fin N) ℂ) (marks : List (Fin N × Fin N))
    (a : ℝ) (ha : 0<a) (hK : ∀ i j, ‖K i j‖ ≤ a) :
    ‖preferredMarkedMinor K marks‖/(N.factorial:ℝ) ≤
      (Real.exp 1/Real.sqrt N)^N*a^(N-marks.length) :=
  markedDeterminant_factorial_bound hN K (fun r => marks.get r) a ha hK

/-- Exact source-specific mixed parameter/coordinate derivative expansion.
Every coefficient is a product of actual regular-kernel jets, and every mark
is a genuine signed determinant derivative. -/
theorem preferred_regular_kernel_mixed_marked_expansion {N k : ℕ}
    (s : ℂ) (q : Fin N → ℂ)
    (hK : ContDiffAt ℂ ∞ (fun z : ℂ × (Fin N → ℂ) => preferredRegularKernel z.1 z.2) (s,q))
    (v : Fin k → ℂ × (Fin N → ℂ)) :
    iteratedFDeriv ℂ k (fun z : ℂ × (Fin N → ℂ) => (preferredRegularKernel z.1 z.2).det) (s,q) v =
      ∑ c : OrderedFinpartition k, ∑ marks : Fin c.length → Fin N × Fin N,
        (∏ r, partitionKernelDirections
          (fun z : ℂ × (Fin N → ℂ) => preferredRegularKernel z.1 z.2)
          (s,q) c v r (marks r).1 (marks r).2) *
          preferredMarkedMinor (preferredRegularKernel s q) (List.ofFn marks) := by
  simp_rw [preferredMarkedMinor_ofFn]
  exact composite_determinant_jet_marked_expansion _ (s,q) hK v

theorem preferred_regular_kernel_mark_count {N k : ℕ}
    (c : OrderedFinpartition k) (marks : Fin c.length → Fin N × Fin N) :
    (List.ofFn marks).length ≤ k := by
  simpa only [List.length_ofFn] using c.length_le

theorem preferred_regular_kernel_loss_mark_budget {N k j h : ℕ}
    (hkj : h+k≤2*j) (c : OrderedFinpartition k)
    (marks : Fin c.length → Fin N × Fin N) :
    h+(List.ofFn marks).length ≤ 2*j :=
  (Nat.add_le_add_left (preferred_regular_kernel_mark_count c marks) h).trans hkj

def preferredKernelJetSupport (N k : ℕ) : Finset (List (Fin N × Fin N)) :=
  Finset.univ.image (fun z : MarkedJetIndex N k => List.ofFn z.2)

theorem preferredKernelJetSupport_card (N k : ℕ) (hN : 1≤N) :
    (preferredKernelJetSupport N k).card ≤
      Fintype.card (OrderedFinpartition k)*N^(2*k) := by
  classical
  exact (Finset.card_image_le).trans (by
    simpa only [Finset.card_univ] using marked_jet_index_card_le N k hN)

theorem preferredKernelJetSupport_length {N k : ℕ} {marks : List (Fin N × Fin N)}
    (hm : marks ∈ preferredKernelJetSupport N k) : marks.length ≤ k := by
  classical
  obtain ⟨z,_,rfl⟩ := Finset.mem_image.mp hm
  exact preferred_regular_kernel_mark_count z.1 z.2

theorem preferredKernelJetSupport_polynomial_count (k : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ N : ℕ, 1≤N →
      ((preferredKernelJetSupport N k).card:ℝ) ≤ C*(N:ℝ)^(2*k) := by
  refine ⟨Fintype.card (OrderedFinpartition k), ?_, ?_⟩
  · exact_mod_cast Fintype.card_pos (α := OrderedFinpartition k)
  · intro N hN
    exact_mod_cast preferredKernelJetSupport_card N k hN

/-- The grouped coefficient is an explicit finite sum of products of actual
kernel jets, rather than an existential scalar weight. -/
def preferredKernelJetCoefficient {N k : ℕ} (s : ℂ) (q : Fin N → ℂ)
    (v : Fin k → ℂ × (Fin N → ℂ)) (marks : List (Fin N × Fin N)) : ℂ :=
  ∑ z : MarkedJetIndex N k with List.ofFn z.2 = marks,
    ∏ r, partitionKernelDirections
      (fun z : ℂ × (Fin N → ℂ) => preferredRegularKernel z.1 z.2)
      (s,q) z.1 v r (z.2 r).1 (z.2 r).2

theorem preferred_regular_kernel_grouped_marked_expansion {N k : ℕ}
    (s : ℂ) (q : Fin N → ℂ)
    (hK : ContDiffAt ℂ ∞ (fun z : ℂ × (Fin N → ℂ) => preferredRegularKernel z.1 z.2) (s,q))
    (v : Fin k → ℂ × (Fin N → ℂ)) :
    iteratedFDeriv ℂ k (fun z : ℂ × (Fin N → ℂ) => (preferredRegularKernel z.1 z.2).det) (s,q) v =
      ∑ marks ∈ preferredKernelJetSupport N k,
        preferredKernelJetCoefficient s q v marks *
          preferredMarkedMinor (preferredRegularKernel s q) marks := by
  classical
  rw [preferred_regular_kernel_mixed_marked_expansion s q hK v]
  rw [← Fintype.sum_sigma']
  symm
  simp only [preferredKernelJetCoefficient, Finset.sum_mul]
  calc
    _ = ∑ marks ∈ preferredKernelJetSupport N k,
        ∑ z : MarkedJetIndex N k with List.ofFn z.2 = marks,
          (∏ r, partitionKernelDirections
            (fun z : ℂ × (Fin N → ℂ) => preferredRegularKernel z.1 z.2)
            (s,q) z.1 v r (z.2 r).1 (z.2 r).2) *
            preferredMarkedMinor (preferredRegularKernel s q) (List.ofFn z.2) := by
      apply Finset.sum_congr rfl
      intro marks _
      apply Finset.sum_congr rfl
      intro z hz
      rw [(Finset.mem_filter.mp hz).2]
    _ = _ := Finset.sum_fiberwise_of_maps_to
      (fun z hz => Finset.mem_image.mpr ⟨z,hz,rfl⟩) _

end
end IsingBulk.Preferred22
