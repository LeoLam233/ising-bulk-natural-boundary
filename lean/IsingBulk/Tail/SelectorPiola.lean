import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Topology.Instances.Matrix

/-! Finite-dimensional determinant calculus for the source homotopy.
The cofactor cancellation is algebraic and valid without invertibility. -/
namespace IsingBulk.Tail
noncomputable section
open scoped BigOperators Matrix
set_option backward.isDefEq.respectTransparency false

 def rowDetContinuous (N : ℕ) : ContinuousMultilinearMap ℝ
    (fun _ : Fin N => Fin N → ℂ) ℂ where
  toMultilinearMap :=
    (Matrix.detRowAlternating : (Fin N → ℂ) [⋀^Fin N]→ₗ[ℂ] ℂ).toMultilinearMap.restrictScalars ℝ
  cont := continuous_id.matrix_det

 theorem hasDerivAt_det_rows {N : ℕ} (A : ℝ → Matrix (Fin N) (Fin N) ℂ)
    (A' : Matrix (Fin N) (Fin N) ℂ) (t : ℝ)
    (hA : ∀ i j, HasDerivAt (fun u => A u i j) (A' i j) t) :
    HasDerivAt (fun u => (A u).det) (∑ i, ((A t).updateRow i (A' i)).det) t := by
  have hm : HasDerivAt A A' t := hasDerivAt_pi.mpr (fun i => hasDerivAt_pi.mpr (hA i))
  have hd := ((rowDetContinuous N).hasFDerivAt (A t)).comp_hasDerivAt t hm
  convert hd using 1
  · rfl
  · rw [ContinuousMultilinearMap.linearDeriv_apply]
    rfl

 theorem hasDerivAt_det_columns {N : ℕ} (A : ℝ → Matrix (Fin N) (Fin N) ℂ)
    (A' : Matrix (Fin N) (Fin N) ℂ) (t : ℝ)
    (hA : ∀ i j, HasDerivAt (fun u => A u i j) (A' i j) t) :
    HasDerivAt (fun u => (A u).det)
      (∑ i, ((A t).updateCol i (fun j => A' j i)).det) t := by
  have hd := hasDerivAt_det_rows (fun u => (A u).transpose) A'.transpose t (fun i j => hA j i)
  have he : ∀ i, A'.transpose i = fun j => A' j i := fun _ => rfl
  simpa only [Matrix.det_transpose, Matrix.updateRow_transpose, he] using hd

 theorem det_double_updateCol_neg {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ)
    {i j : Fin N} (hij : i ≠ j) (u v : Fin N → ℂ) :
    ((A.updateCol i u).updateCol j v).det =
      -((A.updateCol j u).updateCol i v).det := by
  rw [← Matrix.det_transpose, ← Matrix.det_transpose (A.updateCol j u |>.updateCol i v)]
  simp only [← Matrix.updateRow_transpose]
  have he : Function.update (Function.update A.transpose i u) j v =
      (Function.update (Function.update A.transpose j u) i v) ∘ Equiv.swap i j := by
    funext k
    by_cases hki : k=i
    · subst k; simp [hij, Ne.symm hij]
    · by_cases hkj : k=j
      · subst k; simp
      · simp [hki,hkj,Equiv.swap_apply_of_ne_of_ne hki hkj]
  change Matrix.det (Function.update (Function.update A.transpose i u) j v) =
    -Matrix.det (Function.update (Function.update A.transpose j u) i v)
  rw [he]
  exact (Matrix.detRowAlternating : (Fin N → ℂ) [⋀^Fin N]→ₗ[ℂ] ℂ).map_swap _ hij

 theorem piola_algebraic_cancellation {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ)
    (v : Fin N → ℂ) (H : Fin N → Fin N → Fin N → ℂ)
    (hH : ∀ i j, H i j=H j i) :
    (∑ i, ∑ j, if i=j then 0 else ((A.updateCol i v).updateCol j (H i j)).det) = 0 := by
  let F : Fin N → Fin N → ℂ := fun i j =>
    if i=j then 0 else ((A.updateCol i v).updateCol j (H i j)).det
  have hanti : ∀ i j, F i j = -F j i := by
    intro i j
    by_cases hij : i=j
    · subst j; simp [F]
    · dsimp [F]
      rw [ite_eq_right hij, ite_eq_right (Ne.symm hij), hH i j]
      exact det_double_updateCol_neg A hij v (H j i)
  have he : (∑ i, ∑ j, F i j) = -(∑ i, ∑ j, F i j) := by
    calc
      _ = ∑ j, ∑ i, F i j := Finset.sum_comm
      _ = ∑ j, ∑ i, -F j i := by
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro i _
        exact hanti i j
      _ = _ := by simp
  change (∑ i, ∑ j, F i j)=0
  have hr := congrArg Complex.re he
  have hi := congrArg Complex.im he
  apply Complex.ext <;> simp only [Complex.zero_re, Complex.zero_im]
  · simp only [Complex.neg_re] at hr; linarith
  · simp only [Complex.neg_im] at hi; linarith

 theorem cofactor_gradient_identity {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ)
    (v : Fin N → ℂ) (L : (Fin N → ℂ) →ₗ[ℂ] ℂ) :
    L v*A.det = ∑ i, L (fun j => A j i)*(A.updateCol i v).det := by
  have he : (∑ i, (A.cramer v i) • (fun j => A j i)) = A.det • v := by
    have hh := Matrix.mulVec_cramer A v
    convert hh using 1
    funext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hh := congrArg L he
  simp only [map_sum, map_smul, smul_eq_mul, Matrix.cramer_apply] at hh
  simpa only [mul_comm] using hh.symm

 theorem hasDerivAt_replacement_minor {N : ℕ}
    (A : ℝ → Matrix (Fin N) (Fin N) ℂ) (A' : Matrix (Fin N) (Fin N) ℂ)
    (v : ℝ → Fin N → ℂ) (v' : Fin N → ℂ) (t : ℝ) (i : Fin N)
    (hA : ∀ j k, HasDerivAt (fun u => A u j k) (A' j k) t)
    (hv : ∀ j, HasDerivAt (fun u => v u j) (v' j) t) :
    HasDerivAt (fun u => ((A u).updateCol i (v u)).det)
      (((A t).updateCol i v').det +
        ∑ j, if i=j then 0 else
          (((A t).updateCol i (v t)).updateCol j (fun k => A' k j)).det) t := by
  have hd := hasDerivAt_det_columns (fun u => (A u).updateCol i (v u))
    (A'.updateCol i v') t (by
      intro j k
      by_cases hk : k=i
      · subst k; simpa only [Matrix.updateCol_apply, ite_true] using hv j
      · simpa only [Matrix.updateCol_apply, hk, ite_false] using hA j k)
  convert hd using 1
  symm
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have heq : ∀ j, (fun k => A'.updateCol i v' k j) = if j=i then v' else (fun k => A' k j) := by
    intro j
    funext k
    by_cases hj : j=i <;> simp [hj]
  simp only [heq, ite_true, Matrix.updateCol_idem]
  congr 1
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  simp only [ite_true, add_zero]
  apply Finset.sum_congr rfl
  intro j hj
  have hji := Finset.ne_of_mem_erase hj
  simp only [hji, Ne.symm hji, ite_false]

 theorem cofactor_coordinate_divergence {N : ℕ}
    (A : (Fin N → ℝ) → Matrix (Fin N) (Fin N) ℂ)
    (v : (Fin N → ℝ) → Fin N → ℂ) (θ : Fin N → ℝ)
    (L : Matrix (Fin N) (Fin N) ℂ) (H : Fin N → Fin N → Fin N → ℂ)
    (hH : ∀ i j, H i j=H j i)
    (hA : ∀ i k j, HasDerivAt (fun u => A (Function.update θ i u) k j) (H i j k) (θ i))
    (hv : ∀ i k, HasDerivAt (fun u => v (Function.update θ i u) k) (L k i) (θ i)) :
    (∑ i, deriv (fun u => ((A (Function.update θ i u)).updateCol i
      (v (Function.update θ i u))).det) (θ i)) =
      ∑ i, ((A θ).updateCol i (fun k => L k i)).det := by
  have hd (i : Fin N) := hasDerivAt_replacement_minor
    (fun u => A (Function.update θ i u)) (fun k j => H i j k)
    (fun u => v (Function.update θ i u)) (fun k => L k i) (θ i) i (hA i) (hv i)
  have he (i : Fin N) : deriv (fun u => ((A (Function.update θ i u)).updateCol i
      (v (Function.update θ i u))).det) (θ i) =
      ((A θ).updateCol i (fun k => L k i)).det +
        ∑ j, if i=j then 0 else (((A θ).updateCol i (v θ)).updateCol j (H i j)).det := by
    simpa only [Function.update_eq_self] using (hd i).deriv
  simp_rw [he]
  rw [Finset.sum_add_distrib, piola_algebraic_cancellation (A θ) (v θ) H hH, add_zero]

/-- Local holomorphic top-form conservation, expressed entirely in actual
coordinate derivatives. No integral identity is assumed. -/
 theorem pointwise_homotopy_conservation {N : ℕ}
    (G : ℝ → (Fin N → ℝ) → ℂ)
    (A : ℝ → (Fin N → ℝ) → Matrix (Fin N) (Fin N) ℂ)
    (v : (Fin N → ℝ) → Fin N → ℂ) (t : ℝ) (θ : Fin N → ℝ)
    (L : (Fin N → ℂ) →ₗ[ℂ] ℂ) (P : Matrix (Fin N) (Fin N) ℂ)
    (H : Fin N → Fin N → Fin N → ℂ) (hH : ∀ i j, H i j=H j i)
    (hGt : HasDerivAt (fun u => G u θ) (L (v θ)) t)
    (hGx : ∀ i, HasDerivAt (fun u => G t (Function.update θ i u))
      (L (fun j => A t θ j i)) (θ i))
    (hAt : ∀ i j, HasDerivAt (fun u => A u θ i j) (P i j) t)
    (hAx : ∀ i k j, HasDerivAt (fun u => A t (Function.update θ i u) k j) (H i j k) (θ i))
    (hvx : ∀ i k, HasDerivAt (fun u => v (Function.update θ i u) k) (P k i) (θ i)) :
    deriv (fun u => G u θ*(A u θ).det) t =
      ∑ i, deriv (fun u => G t (Function.update θ i u)*
        ((A t (Function.update θ i u)).updateCol i (v (Function.update θ i u))).det) (θ i) := by
  have hdet := hasDerivAt_det_columns (fun u => A u θ) P t hAt
  rw [(hGt.fun_mul hdet).deriv]
  have hm (i : Fin N) := hasDerivAt_replacement_minor
    (fun u => A t (Function.update θ i u)) (fun k j => H i j k)
    (fun u => v (Function.update θ i u)) (fun k => P k i) (θ i) i (hAx i) (hvx i)
  have hd (i : Fin N) := ((hGx i).fun_mul (hm i)).deriv
  simp only [Function.update_eq_self] at hd
  simp_rw [hd]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [Finset.sum_add_distrib, piola_algebraic_cancellation (A t θ) (v θ) H hH, add_zero]
  rw [cofactor_gradient_identity (A t θ) (v θ) L]

end
end IsingBulk.Tail
