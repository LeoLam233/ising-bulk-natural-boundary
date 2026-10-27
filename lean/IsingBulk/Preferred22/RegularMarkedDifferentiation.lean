import IsingBulk.Preferred22.RegularMarkedKernel
import IsingBulk.Preferred22.MarkedMinorDifferentiation

/-! Literal list-indexed marked-minor rules for the actual transport code.
The complex parameter and real angular chain rules use the same signed
complementary minors, adding one actual matrix-entry mark per derivative. -/
namespace IsingBulk.Preferred22
noncomputable section
open scoped BigOperators ContDiff Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false

theorem preferredMarkedMinor_cons_eq {N : ℕ}
    (K : Matrix (Fin N) (Fin N) ℂ) (a : Fin N × Fin N)
    (marks : List (Fin N × Fin N)) :
    preferredMarkedMinor K (a::marks) = markedDeterminant K (Fin.cons a marks.get) := by
  simpa only [List.ofFn_cons, List.ofFn_get] using
    preferredMarkedMinor_ofFn K (Fin.cons a marks.get)

theorem preferredMarkedMinor_contDiff {N : ℕ} (marks : List (Fin N × Fin N)) :
    ContDiff ℂ ∞ (fun K : Matrix (Fin N) (Fin N) ℂ => preferredMarkedMinor K marks) :=
  markedDeterminant_contDiff marks.get

theorem preferredMarkedMinor_fderiv {N : ℕ}
    (K B : Matrix (Fin N) (Fin N) ℂ) (marks : List (Fin N × Fin N)) :
    fderiv ℂ (fun A => preferredMarkedMinor A marks) K B =
      ∑ a : Fin N × Fin N, B a.1 a.2 * preferredMarkedMinor K (a::marks) := by
  simp_rw [preferredMarkedMinor_cons_eq]
  exact markedDeterminant_fderiv K B marks.get

theorem preferredMarkedMinor_comp_fderiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {N : ℕ} (K : E → Matrix (Fin N) (Fin N) ℂ) (x v : E)
    (hK : DifferentiableAt ℂ K x) (marks : List (Fin N × Fin N)) :
    fderiv ℂ (fun y => preferredMarkedMinor (K y) marks) x v =
      ∑ a : Fin N × Fin N, (fderiv ℂ K x v) a.1 a.2 * preferredMarkedMinor (K x) (a::marks) := by
  simp_rw [preferredMarkedMinor_cons_eq]
  exact markedDeterminant_comp_fderiv K x v hK marks.get

theorem preferredMarkedMinor_comp_real_fderiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {N : ℕ} (K : E → Matrix (Fin N) (Fin N) ℂ) (x v : E)
    (hK : DifferentiableAt ℝ K x) (marks : List (Fin N × Fin N)) :
    fderiv ℝ (fun y => preferredMarkedMinor (K y) marks) x v =
      ∑ a : Fin N × Fin N, (fderiv ℝ K x v) a.1 a.2 * preferredMarkedMinor (K x) (a::marks) := by
  simp_rw [preferredMarkedMinor_cons_eq]
  exact markedDeterminant_comp_real_fderiv K x v hK marks.get

end
end IsingBulk.Preferred22
