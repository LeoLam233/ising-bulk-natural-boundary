import IsingBulk.Preferred22.RegularTransport
import IsingBulk.Preferred22.RegularMarkedDifferentiation

/-! Exact signed-minor recursion for the literal regular transport generator.
The coefficients below are actual source derivatives. Uniform coefficient
bounds and the identification of all regular descendants with the physical
transported density remain separate analytic obligations. -/
namespace IsingBulk.Preferred22
noncomputable section
open scoped BigOperators ContDiff Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false

/-- The actual regular kernel pulled back to the original angular variables. -/
def preferredSourceRegularKernel {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (s : ℂ) (θ : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  preferredRegularKernel s (preferredSourceCoordinate τ p m s θ)

/-- The actual material derivative of one pulled-back matrix entry. The
coordinate part uses real derivatives, exactly as in the source generator. -/
def preferredKernelMaterialEntry {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (s : ℂ) (θ : Fin N → ℝ) (a : Fin N × Fin N) : ℂ :=
  (deriv (fun t : ℂ => preferredSourceRegularKernel τ p m t θ) s) a.1 a.2 -
    ∑ i, preferredSourceAngularField .right τ p m s θ i *
      (deriv (fun x : ℝ => preferredSourceRegularKernel τ p m s (Function.update θ i x))
        (θ i)) a.1 a.2

theorem sum_material_product {N : ℕ} (V a b : Fin N → ℂ) (u v : ℂ) :
    (∑ i, V i*(a i*v+u*b i)) = (∑ i, V i*a i)*v+u*(∑ i, V i*b i) := by
  calc
    _ = ∑ i, ((V i*a i)*v+u*(V i*b i)) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by simp only [Finset.sum_add_distrib,Finset.sum_mul,Finset.mul_sum]

/-- The zero-order regular divergence belongs to the coefficient derivative
exactly once; the second factor receives only the material derivative. -/
theorem preferredRegularTransportStep_mul {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (A G : ℂ → (Fin N → ℝ) → ℂ) (s : ℂ) (θ : Fin N → ℝ)
    (hAs : DifferentiableAt ℂ (fun t => A t θ) s)
    (hGs : DifferentiableAt ℂ (fun t => G t θ) s)
    (hAθ : ∀ i, DifferentiableAt ℝ (fun x => A s (Function.update θ i x)) (θ i))
    (hGθ : ∀ i, DifferentiableAt ℝ (fun x => G s (Function.update θ i x)) (θ i)) :
    preferredRegularTransportStep τ p m (fun t x => A t x*G t x) s θ =
      preferredRegularTransportStep τ p m A s θ*G s θ + A s θ *
        (deriv (fun t : ℂ => G t θ) s -
          ∑ i, preferredSourceAngularField .right τ p m s θ i *
            deriv (fun x : ℝ => G s (Function.update θ i x)) (θ i)) := by
  have hs := (hAs.hasDerivAt.fun_mul hGs.hasDerivAt).deriv
  have hx (i : Fin N) := ((hAθ i).hasDerivAt.fun_mul (hGθ i).hasDerivAt).deriv
  simp only [Function.update_eq_self] at hx
  rw [preferredRegularTransportStep_eq,preferredRegularTransportStep_eq,hs]
  simp_rw [hx]
  rw [sum_material_product]
  ring

/-- Exact one-step marked recursion. Every new determinant mark is attached
to the actual material derivative of its matrix entry, and collisions are
handled by the signed complementary minor itself. -/
theorem preferredRegularTransportStep_marked {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (A : ℂ → (Fin N → ℝ) → ℂ) (s : ℂ) (θ : Fin N → ℝ)
    (marks : List (Fin N × Fin N))
    (hAs : DifferentiableAt ℂ (fun t => A t θ) s)
    (hAθ : ∀ i, DifferentiableAt ℝ (fun x => A s (Function.update θ i x)) (θ i))
    (hKs : DifferentiableAt ℂ (fun t => preferredSourceRegularKernel τ p m t θ) s)
    (hKθ : ∀ i, DifferentiableAt ℝ
      (fun x => preferredSourceRegularKernel τ p m s (Function.update θ i x)) (θ i)) :
    preferredRegularTransportStep τ p m
      (fun t x => A t x * preferredMarkedMinor (preferredSourceRegularKernel τ p m t x) marks) s θ =
      preferredRegularTransportStep τ p m A s θ *
        preferredMarkedMinor (preferredSourceRegularKernel τ p m s θ) marks +
      ∑ a : Fin N × Fin N, (A s θ*preferredKernelMaterialEntry τ p m s θ a) *
        preferredMarkedMinor (preferredSourceRegularKernel τ p m s θ) (a::marks) := by
  have hm := (preferredMarkedMinor_contDiff (N:=N) marks).differentiable (by simp)
  have hGs := hm.differentiableAt.comp s hKs
  have hGθ (i : Fin N) := ((hm.differentiableAt.hasFDerivAt.restrictScalars ℝ).comp
    (θ i) (hKθ i).hasFDerivAt).differentiableAt
  have hs := preferredMarkedMinor_comp_fderiv
    (fun t => preferredSourceRegularKernel τ p m t θ) s 1 hKs marks
  simp only [fderiv_apply_one_eq_deriv] at hs
  have hx (i : Fin N) := preferredMarkedMinor_comp_real_fderiv
    (fun x => preferredSourceRegularKernel τ p m s (Function.update θ i x)) (θ i) 1 (hKθ i) marks
  simp only [fderiv_apply_one_eq_deriv,Function.update_eq_self] at hx
  rw [preferredRegularTransportStep_mul τ p m A _ s θ hAs hGs hAθ hGθ,hs]
  simp_rw [hx]
  unfold preferredKernelMaterialEntry
  simp only [Finset.mul_sum,Finset.sum_mul,Finset.sum_sub_distrib,mul_sub,sub_mul,mul_assoc]
  congr 1
  rw [Finset.sum_comm]

/-- The actual coefficient of the unmarked initial determinant. -/
def preferredRegularSeedCoefficient {N : ℕ} (τ : ℝ) (η p m r : ℝ → ℝ)
    (s : ℂ) (θ : Fin N → ℝ) : ℂ :=
  (preferredCellWeight .right η p m r θ:ℂ) *
    (∏ i, preferredRegularOneBody s (preferredSourceCoordinate τ p m s θ i)) /
    ((N.factorial:ℂ)*(2*Real.pi:ℂ)^(N-1))

theorem preferredRegularSeed_eq_empty_minor {N : ℕ} (τ : ℝ) (η p m r : ℝ → ℝ)
    (s : ℂ) (θ : Fin N → ℝ) :
    preferredRegularSeed τ η p m r s θ =
      preferredRegularSeedCoefficient τ η p m r s θ *
        preferredMarkedMinor (preferredSourceRegularKernel τ p m s θ) [] := by
  simp only [preferredMarkedMinor,List.length_nil,iteratedFDeriv_zero_apply]
  unfold preferredRegularSeed preferredRegularSeedCoefficient preferredSourceRegularKernel
  ring

end
end IsingBulk.Preferred22
