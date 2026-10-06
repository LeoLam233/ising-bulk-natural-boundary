import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! Real differentials of permutation-invariant scalar functions on the
coordinate diagonal, with complex values allowed. -/
namespace IsingBulk.Tail
noncomputable section
open scoped BigOperators

def coordinatePermutationLinear {N : ℕ} (sigma : Equiv.Perm (Fin N)) :
    (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) :=
  ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj (sigma i))

theorem coordinateSwap_fixed {N : ℕ} (i j : Fin N) (x : Fin N → ℝ) (hij : x i=x j) :
    coordinatePermutationLinear (Equiv.swap i j) x=x := by
  funext k
  change x (Equiv.swap i j k)=x k
  by_cases hki : k=i
  · subst k; rw [Equiv.swap_apply_left]; exact hij.symm
  · by_cases hkj : k=j
    · subst k; rw [Equiv.swap_apply_right]; exact hij
    · rw [Equiv.swap_apply_of_ne_of_ne hki hkj]

theorem coordinateSwap_single {N : ℕ} (i j : Fin N) :
    coordinatePermutationLinear (Equiv.swap i j) (Pi.single i (1:ℝ))=Pi.single j 1 := by
  funext k
  change (Pi.single i (1:ℝ) : Fin N → ℝ) (Equiv.swap i j k)=(Pi.single j (1:ℝ) : Fin N → ℝ) k
  by_cases hki : k=i
  · subst k
    rw [Equiv.swap_apply_left]
    by_cases hij : i=j
    · subst j; rfl
    · simp [hij,Ne.symm hij]
  · by_cases hkj : k=j
    · subst k
      simp only [Equiv.swap_apply_right,Pi.single_eq_same]
    · rw [Equiv.swap_apply_of_ne_of_ne hki hkj]
      simp [hki,hkj]

theorem symmetric_coordinate_derivatives_equal {N : ℕ} (F : (Fin N → ℝ) → ℂ)
    (hsym : ∀ sigma : Equiv.Perm (Fin N), ∀ x, F (fun k => x (sigma k))=F x)
    (x : Fin N → ℝ) (hF : DifferentiableAt ℝ F x) (i j : Fin N) (hij : x i=x j) :
    fderiv ℝ F x (Pi.single i 1)=fderiv ℝ F x (Pi.single j 1) := by
  let T := coordinatePermutationLinear (Equiv.swap i j)
  have hx : T x=x := coordinateSwap_fixed i j x hij
  have hd : HasFDerivAt F (fderiv ℝ F x) (T x) := by rw [hx]; exact hF.hasFDerivAt
  have hc := hd.comp x T.hasFDerivAt
  have he : F ∘ T=F := by funext y; exact hsym (Equiv.swap i j) y
  rw [he] at hc
  have hmap := hF.hasFDerivAt.unique hc
  have hh := congrArg (fun L : (Fin N → ℝ) →L[ℝ] ℂ => L (Pi.single i 1)) hmap
  simpa only [ContinuousLinearMap.comp_apply,T,coordinateSwap_single] using hh

theorem symmetric_diagonal_fderiv_zero {N : ℕ} (hN : 0 < N) (F : (Fin N → ℝ) → ℂ)
    (hsym : ∀ sigma : Equiv.Perm (Fin N), ∀ x, F (fun k => x (sigma k))=F x)
    (t : ℝ) (hF : DifferentiableAt ℝ F (fun _ => t)) (omega : Fin N → ℝ)
    (hsum : ∑ i, omega i=0) :
    fderiv ℝ F (fun _ => t) omega=0 := by
  let q : Fin N := ⟨0,hN⟩
  let L := fderiv ℝ F (fun _ => t)
  have he (i : Fin N) : L (Pi.single i 1)=L (Pi.single q 1) :=
    symmetric_coordinate_derivatives_equal F hsym (fun _ => t) hF i q rfl
  have hd : omega=∑ i, omega i • Pi.single i (1:ℝ) := by
    rw [← Finset.univ_sum_single omega]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Pi.single_smul]
    simp
  change L omega=0
  rw [hd,map_sum]
  simp only [map_smul,he,← Finset.sum_smul,hsum,zero_smul]

end
end IsingBulk.Tail
