import IsingBulk.HT22.Tail.ScalarTransport
import IsingBulk.HT22.Algebra.BorderedMinorDifferentiation

/-! # Actual bordered marked-minor transport

Only the generic derivative rule for the determinant polynomial is reused.
The source matrix and material operator are the literal HT22 objects.
-/
namespace IsingBulk.HT22.Tail
noncomputable section
open IsingBulk.Preferred22
open scoped BigOperators ContDiff Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false

/-- A marked derivative of the actual (N+1)-dimensional bordered determinant. -/
def borderedMarkedMinor {N ell : ℕ} (K : Matrix (Fin (N+1)) (Fin (N+1)) ℂ)
    (marks : Fin ell → Fin (N+1) × Fin (N+1)) : ℂ := markedDeterminant K marks

def kernelMaterialEntry {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (t : ℂ) (θ : Fin N → ℝ) (a : Fin (N+1) × Fin (N+1)) : ℂ :=
  (deriv (fun s : ℂ => sourceBorderedKernel τ p m s θ) t) a.1 a.2 -
    ∑ i, angularField τ p m t θ i *
      (deriv (fun x : ℝ => sourceBorderedKernel τ p m t (Function.update θ i x)) (θ i)) a.1 a.2

/-- Exact product rule: the regular divergence is counted once, never once
per factor. Every angular derivative is over ℝ. -/
theorem regularTransportStep_mul {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (A G : ℂ → (Fin N → ℝ) → ℂ) (t : ℂ) (θ : Fin N → ℝ)
    (hAt : DifferentiableAt ℂ (fun s => A s θ) t)
    (hGt : DifferentiableAt ℂ (fun s => G s θ) t)
    (hAθ : ∀ i, DifferentiableAt ℝ (fun x => A t (Function.update θ i x)) (θ i))
    (hGθ : ∀ i, DifferentiableAt ℝ (fun x => G t (Function.update θ i x)) (θ i)) :
    regularTransportStep τ p m (fun s x => A s x*G s x) t θ =
      regularTransportStep τ p m A t θ*G t θ+A t θ*
        (deriv (fun s : ℂ => G s θ) t-∑ i, angularField τ p m t θ i*
          deriv (fun x : ℝ => G t (Function.update θ i x)) (θ i)) := by
  have ht := (hAt.hasDerivAt.fun_mul hGt.hasDerivAt).deriv
  have hx (i : Fin N) := ((hAθ i).hasDerivAt.fun_mul (hGθ i).hasDerivAt).deriv
  simp only [Function.update_eq_self] at hx
  rw [regularTransportStep_eq,regularTransportStep_eq,ht]
  simp_rw [hx]
  simp only [mul_add,Finset.sum_add_distrib]
  have hs : (∑ i, angularField τ p m t θ i*
      (deriv (fun x : ℝ => A t (Function.update θ i x)) (θ i)*G t θ)) =
      (∑ i, angularField τ p m t θ i*
        deriv (fun x : ℝ => A t (Function.update θ i x)) (θ i))*G t θ := by
    simp only [Finset.sum_mul,mul_assoc]
  have hg : (∑ i, angularField τ p m t θ i*
      (A t θ*deriv (fun x : ℝ => G t (Function.update θ i x)) (θ i))) =
      A t θ*(∑ i, angularField τ p m t θ i*
        deriv (fun x : ℝ => G t (Function.update θ i x)) (θ i)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hs,hg]
  ring

/-- Exact one-step recursion with actual matrix-entry material derivatives.
The only hypotheses are the local differentiability cuts needed by the
ordinary product and chain rules; no bound on a minor or descendant is assumed. -/
theorem regularTransportStep_marked {N ell : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (A : ℂ → (Fin N → ℝ) → ℂ) (t : ℂ) (θ : Fin N → ℝ)
    (marks : Fin ell → Fin (N+1) × Fin (N+1))
    (hAt : DifferentiableAt ℂ (fun s => A s θ) t)
    (hAθ : ∀ i, DifferentiableAt ℝ (fun x => A t (Function.update θ i x)) (θ i))
    (hKt : DifferentiableAt ℂ (fun s => sourceBorderedKernel τ p m s θ) t)
    (hKθ : ∀ i, DifferentiableAt ℝ
      (fun x => sourceBorderedKernel τ p m t (Function.update θ i x)) (θ i)) :
    regularTransportStep τ p m
      (fun s x => A s x*borderedMarkedMinor (sourceBorderedKernel τ p m s x) marks) t θ =
      regularTransportStep τ p m A t θ * borderedMarkedMinor (sourceBorderedKernel τ p m t θ) marks +
      ∑ a : Fin (N+1) × Fin (N+1),
        (A t θ*kernelMaterialEntry τ p m t θ a)*
          borderedMarkedMinor (sourceBorderedKernel τ p m t θ) (Fin.cons a marks) := by
  have hm := (markedDeterminant_contDiff marks).differentiable (by simp)
  have hGt := hm.differentiableAt.comp t hKt
  have hGθ (i : Fin N) := ((hm.differentiableAt.hasFDerivAt.restrictScalars ℝ).comp
    (θ i) (hKθ i).hasFDerivAt).differentiableAt
  have ht := markedDeterminant_comp_fderiv
    (fun s => sourceBorderedKernel τ p m s θ) t 1 hKt marks
  simp only [fderiv_apply_one_eq_deriv] at ht
  have hx (i : Fin N) := markedDeterminant_comp_real_fderiv
    (fun x => sourceBorderedKernel τ p m t (Function.update θ i x)) (θ i) 1 (hKθ i) marks
  simp only [fderiv_apply_one_eq_deriv,Function.update_eq_self] at hx
  unfold borderedMarkedMinor
  rw [regularTransportStep_mul τ p m A _ t θ hAt hGt hAθ hGθ,ht]
  simp_rw [hx]
  unfold kernelMaterialEntry
  simp only [Finset.mul_sum,Finset.sum_mul,Finset.sum_sub_distrib,mul_sub,sub_mul,mul_assoc]
  congr 1
  rw [Finset.sum_comm]

/-- Only the N by N ordinary block varies; both ghost borders are constant. -/
def sourceOrdinaryKernel {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (t : ℂ) (θ : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  regularOrdinaryKernel t (sourceCoordinate τ p m t θ)

def ordinaryMaterialEntry {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (t : ℂ) (θ : Fin N → ℝ) (a : Fin N × Fin N) : ℂ :=
  (deriv (fun s : ℂ => sourceOrdinaryKernel τ p m s θ) t) a.1 a.2 -
    ∑ i, angularField τ p m t θ i *
      (deriv (fun x : ℝ => sourceOrdinaryKernel τ p m t (Function.update θ i x)) (θ i)) a.1 a.2

/-- The sharp recursion marks only actual ordinary entries, N² choices.
The ghost derivatives vanish by the algebraic affine-border construction. -/
theorem regularTransportStep_ordinary_marked {N ell : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (A : ℂ → (Fin N → ℝ) → ℂ) (t : ℂ) (θ : Fin N → ℝ)
    (marks : Fin ell → Fin N × Fin N)
    (hAt : DifferentiableAt ℂ (fun s => A s θ) t)
    (hAθ : ∀ i, DifferentiableAt ℝ (fun x => A t (Function.update θ i x)) (θ i))
    (hKt : DifferentiableAt ℂ (fun s => sourceOrdinaryKernel τ p m s θ) t)
    (hKθ : ∀ i, DifferentiableAt ℝ
      (fun x => sourceOrdinaryKernel τ p m t (Function.update θ i x)) (θ i)) :
    regularTransportStep τ p m
      (fun s x => A s x*Algebra.borderedMarkedDeterminant (sourceOrdinaryKernel τ p m s x) marks) t θ =
      regularTransportStep τ p m A t θ * Algebra.borderedMarkedDeterminant (sourceOrdinaryKernel τ p m t θ) marks +
      ∑ a : Fin N × Fin N,
        (A t θ*ordinaryMaterialEntry τ p m t θ a)*
          Algebra.borderedMarkedDeterminant (sourceOrdinaryKernel τ p m t θ) (Fin.cons a marks) := by
  have hg : ContDiff ℂ ∞ (fun K : Matrix (Fin N) (Fin N) ℂ => Algebra.ghostBorder K (fun _ => 1)) := by
    have he : (fun K : Matrix (Fin N) (Fin N) ℂ => Algebra.ghostBorder K (fun _ => 1))=
        (fun K => Algebra.ordinaryDirectionCLM N K+Algebra.ghostBorder 0 (fun _ => 1)) :=
      funext Algebra.ghostBorder_eq_affine
    rw [he]
    exact (Algebra.ordinaryDirectionCLM N).contDiff.add contDiff_const
  have hm := ((markedDeterminant_contDiff (Algebra.ordinaryMarks marks)).comp hg).differentiable (by simp)
  have hGt := hm.differentiableAt.comp t hKt
  have hGθ (i : Fin N) := ((hm.differentiableAt.hasFDerivAt.restrictScalars ℝ).comp
    (θ i) (hKθ i).hasFDerivAt).differentiableAt
  have ht := Algebra.borderedMarkedDeterminant_comp_fderiv
    (fun s => sourceOrdinaryKernel τ p m s θ) t 1 hKt marks
  simp only [fderiv_apply_one_eq_deriv] at ht
  have hx (i : Fin N) := Algebra.borderedMarkedDeterminant_comp_real_fderiv
    (fun x => sourceOrdinaryKernel τ p m t (Function.update θ i x)) (θ i) 1 (hKθ i) marks
  simp only [fderiv_apply_one_eq_deriv,Function.update_eq_self] at hx
  rw [regularTransportStep_mul τ p m A _ t θ hAt hGt hAθ hGθ,ht]
  simp_rw [hx]
  unfold ordinaryMaterialEntry
  simp only [Finset.mul_sum,Finset.sum_mul,Finset.sum_sub_distrib,mul_sub,sub_mul,mul_assoc]
  congr 1
  rw [Finset.sum_comm]

end
end IsingBulk.HT22.Tail
