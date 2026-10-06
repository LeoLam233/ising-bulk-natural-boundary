import IsingBulk.Tail.MicrocoreLaplace
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod

/-! Fubini attachment of one-body Laplace bounds to the actual simple
sum kernel. Joint integrability is proved before interchanging the integrals. -/
namespace IsingBulk.Tail
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators

 theorem laplace_product_kernel_bound (N : ℕ) (hN : 0 < N)
    (μ : Measure ℝ) [SigmaFinite μ] (a f : ℝ → ℝ)
    (ha : Continuous a) (hf : Continuous f) (haPos : ∀ u, 0 < a u) (hfNonneg : ∀ u, 0 ≤ f u)
    (K b : ℝ) (_hK : 0 ≤ K) (_hb : 0 < b)
    (hprofile : IntegrableOn (fun t : ℝ => (min b t⁻¹)^N) (Ioi 0))
    (hbody : ∀ t : ℝ, 0 < t →
      Integrable (fun u => Real.exp (-t*a u)*f u) μ ∧
      (∫ u, Real.exp (-t*a u)*f u ∂μ) ≤ K*min b t⁻¹) :
    Integrable (fun x : Fin N → ℝ => (∏ i, f (x i))/(∑ i, a (x i))) (Measure.pi (fun _ => μ)) ∧
    (∫ x : Fin N → ℝ, (∏ i, f (x i))/(∑ i, a (x i)) ∂Measure.pi (fun _ => μ)) ≤
      K^N*(∫ t : ℝ in Ioi 0, (min b t⁻¹)^N) := by
  let ν : Measure (Fin N → ℝ) := Measure.pi (fun _ => μ)
  let μt : Measure ℝ := volume.restrict (Ioi 0)
  let F : ℝ × (Fin N → ℝ) → ℝ := fun p => ∏ i, Real.exp (-p.1*a (p.2 i))*f (p.2 i)
  have hFc : Continuous F := by unfold F; fun_prop
  have hFm : AEStronglyMeasurable F (μt.prod ν) := hFc.aestronglyMeasurable
  have hF0 : ∀ t x, 0 ≤ F (t,x) := by
    intro t x
    exact Finset.prod_nonneg (fun i _ => mul_nonneg (Real.exp_pos _).le (hfNonneg _))
  have hFnorm : ∀ p, ‖F p‖=F p := fun p => Real.norm_of_nonneg (hF0 p.1 p.2)
  have hinner (t : ℝ) : (∫ x, F (t,x) ∂ν)=(∫ u, Real.exp (-t*a u)*f u ∂μ)^N := by
    simpa only [Fintype.card_fin] using
      (integral_fintype_prod_eq_pow (ι := Fin N) (μ := μ) (fun u => Real.exp (-t*a u)*f u))
  have hbound : ∀ t > 0, (∫ x, F (t,x) ∂ν) ≤ K^N*(min b t⁻¹)^N := by
    intro t ht
    rw [hinner,← mul_pow]
    exact pow_le_pow_left₀ (integral_nonneg (fun u => mul_nonneg (Real.exp_pos _).le (hfNonneg u)))
      (hbody t ht).2 N
  have hgp : Integrable (fun t : ℝ => K^N*(min b t⁻¹)^N) μt := hprofile.const_mul _
  have hnormInt : Integrable (fun t => ∫ x, ‖F (t,x)‖ ∂ν) μt := by
    apply hgp.mono' hFm.norm.integral_prod_right'
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simp only [hFnorm]
    rw [Real.norm_of_nonneg (integral_nonneg (hF0 t))]
    exact hbound t ht
  have hJoint : Integrable F (μt.prod ν) := by
    apply (integrable_prod_iff hFm).mpr
    refine ⟨?_,hnormInt⟩
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact Integrable.fintype_prod (fun _ : Fin N => (hbody t ht).1)
  have hkernel (x : Fin N → ℝ) : (∫ t, F (t,x) ∂μt)=(∏ i, f (x i))/(∑ i, a (x i)) := by
    have hsum : 0 < ∑ i, a (x i) := by
      have hne : (Finset.univ : Finset (Fin N)).Nonempty := ⟨⟨0,hN⟩,Finset.mem_univ _⟩
      exact Finset.sum_pos (fun i _ => haPos _) hne
    have he : ∀ t, F (t,x)=Real.exp (-(∑ i, a (x i))*t)*(∏ i, f (x i)) := by
      intro t
      unfold F
      rw [Finset.prod_mul_distrib,← Real.exp_sum]
      congr 2
      rw [← Finset.mul_sum]
      ring
    simp_rw [he]
    rw [integral_mul_const]
    have hh := integral_exp_mul_Ioi (neg_neg_of_pos hsum) (0:ℝ)
    change (∫ t in Ioi (0:ℝ), Real.exp (-(∑ i, a (x i))*t))*(∏ i, f (x i))=_
    rw [hh]
    simp
    ring
  have hkInt : Integrable (fun x : Fin N → ℝ => (∏ i, f (x i))/(∑ i, a (x i))) ν := by
    have hh := hJoint.integral_prod_right
    simpa only [hkernel] using hh
  refine ⟨hkInt,?_⟩
  have hswap := integral_integral_swap (f := fun t x => F (t,x)) hJoint
  simp only [hkernel] at hswap
  rw [← hswap,← integral_const_mul]
  apply integral_mono_ae hJoint.integral_prod_left hgp
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact hbound t ht

 theorem laplace_product_kernel_power_bound (n : ℕ)
    (μ : Measure ℝ) [SigmaFinite μ] (a f : ℝ → ℝ)
    (ha : Continuous a) (hf : Continuous f) (haPos : ∀ u, 0 < a u) (hfNonneg : ∀ u, 0 ≤ f u)
    (K b : ℝ) (hK : 0 ≤ K) (hb : 0 < b)
    (hbody : ∀ t : ℝ, 0 < t →
      Integrable (fun u => Real.exp (-t*a u)*f u) μ ∧
      (∫ u, Real.exp (-t*a u)*f u ∂μ) ≤ K*min b t⁻¹) :
    Integrable (fun x : Fin (n+2) → ℝ => (∏ i, f (x i))/(∑ i, a (x i)))
      (Measure.pi (fun _ => μ)) ∧
    (∫ x : Fin (n+2) → ℝ, (∏ i, f (x i))/(∑ i, a (x i)) ∂Measure.pi (fun _ => μ)) ≤
      2*K^(n+2)*b^(n+1) := by
  obtain ⟨hi,hbnd⟩ := laplace_product_kernel_bound (n+2) (by omega) μ a f ha hf haPos hfNonneg
    K b hK hb (microcore_laplace_min_integrable n hb) hbody
  refine ⟨hi,hbnd.trans ?_⟩
  calc
    K^(n+2)*(∫ t : ℝ in Ioi 0, (min b t⁻¹)^(n+2)) ≤ K^(n+2)*(2*b^(n+1)) :=
      mul_le_mul_of_nonneg_left (microcore_laplace_min_bound n hb) (pow_nonneg hK _)
    _ = _ := by ring

end
end IsingBulk.Tail
