import IsingBulk.Tail.CoareaRectangleKernel

/-!
HT-1.0 Appendix A: signed periodic kernels and the order of coarea.
Phase translation accounts for the minus sign. Period wrapping is counted
by the explicit interval counts, separately from injectivity of the actual
unwrapped two-phase map. No differentiation of a sign cell occurs here.
-/
namespace IsingBulk.HT.Lie
noncomputable section
open Set MeasureTheory IsingBulk.Tail

/-- A constant unit phase rotates the phase argument, with no change of
attenuation. In particular α=π is the negative HT sign. -/
theorem unit_phase_denominator (r t α : ℝ) :
    ‖1 - Complex.exp (Complex.I*(α:ℂ)) * (r:ℂ) *
      Complex.exp (Complex.I*(t:ℂ))‖ = phaseDenominator r (t+α) := by
  unfold phaseDenominator
  congr 1
  rw [Complex.ofReal_add, mul_add, Complex.exp_add]
  ring

theorem negative_phase_denominator (r t : ℝ) :
    ‖1 + (r:ℂ)*Complex.exp (Complex.I*(t:ℂ))‖ =
      phaseDenominator r (t+Real.pi) := by
  have h := unit_phase_denominator r t Real.pi
  rw [mul_comm Complex.I (Real.pi:ℂ), Complex.exp_pi_mul_I] at h
  simpa using h

/-- Translation is explicit, so the same definition handles both signs
and permits arbitrary offsets of an unwrapped phase image. -/
def shiftedPhaseKernel (a α t : ℝ) : ℝ :=
  (phaseDenominator (Real.exp (-a)) (t+α))⁻¹

theorem shiftedPhaseKernel_nonneg (a α t : ℝ) :
    0 ≤ shiftedPhaseKernel a α t := by
  unfold shiftedPhaseKernel phaseDenominator
  positivity

theorem shiftedPhaseKernel_continuous {a : ℝ} (ha : 0 < a) (α : ℝ) :
    Continuous (shiftedPhaseKernel a α) :=
  (simple_kernel_continuous ha).comp (continuous_id.add continuous_const)

/-- The negative kernel has the same logarithmic integral estimate as the
positive kernel, even on an interval that wraps around many periods. -/
theorem shifted_kernel_interval_integral {a x y : ℝ} (ha : 0 < a)
    (ha1 : a ≤ 1) (α : ℝ) (n : ℕ) (hxy : x ≤ y)
    (hlen : y ≤ x+(n:ℝ)*(2*Real.pi)) :
    (∫ t : ℝ in x..y, shiftedPhaseKernel a α t) ≤
      (n:ℝ)*simpleKernelConstant*(1+|Real.log a|) := by
  unfold shiftedPhaseKernel
  rw [intervalIntegral.integral_comp_add_right
    (f := fun t : ℝ => (phaseDenominator (Real.exp (-a)) t)⁻¹) α]
  exact simple_kernel_interval_integral ha ha1 n (by linarith) (by linarith)

/-- A variable damping is replaced by its floor before integrating.
The factor two from the LT chord estimate is retained. -/
theorem shifted_kernel_radius_floor {r r₀ : ℝ} (hr : 0 ≤ r)
    (hrr : r ≤ r₀) (hr₀ : r₀ < 1) (t α : ℝ) :
    (phaseDenominator r (t+α))⁻¹ ≤ 2*(phaseDenominator r₀ (t+α))⁻¹ :=
  simple_kernel_radius_floor hr hrr hr₀

def shiftedTwoPhaseKernel (a b α β : ℝ) (x : ℝ × ℝ) : ℝ :=
  shiftedPhaseKernel a α x.1 * shiftedPhaseKernel b β x.2

theorem shiftedTwoPhaseKernel_nonneg (a b α β : ℝ) (x : ℝ × ℝ) :
    0 ≤ shiftedTwoPhaseKernel a b α β x :=
  mul_nonneg (shiftedPhaseKernel_nonneg a α x.1)
    (shiftedPhaseKernel_nonneg b β x.2)

theorem shiftedTwoPhaseKernel_continuous {a b : ℝ} (ha : 0 < a)
    (hb : 0 < b) (α β : ℝ) : Continuous (shiftedTwoPhaseKernel a b α β) :=
  ((shiftedPhaseKernel_continuous ha α).comp continuous_fst).mul
    ((shiftedPhaseKernel_continuous hb β).comp continuous_snd)

/-- Explicit signed two-kernel rectangle bound. The period counts nx,ny
remain visible; they must not be conflated with map multiplicity. -/
theorem shifted_two_kernel_rectangle {a b x₀ x₁ y₀ y₁ : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hb : 0 < b) (hb1 : b ≤ 1)
    (α β : ℝ) (nx ny : ℕ) (hx : x₀ ≤ x₁) (hy : y₀ ≤ y₁)
    (hlenx : x₁ ≤ x₀+(nx:ℝ)*(2*Real.pi))
    (hleny : y₁ ≤ y₀+(ny:ℝ)*(2*Real.pi)) :
    IntegrableOn (shiftedTwoPhaseKernel a b α β) (Icc x₀ x₁ ×ˢ Icc y₀ y₁) ∧
      (∫ x in Icc x₀ x₁ ×ˢ Icc y₀ y₁, shiftedTwoPhaseKernel a b α β x) ≤
        ((nx:ℝ)*simpleKernelConstant*(1+|Real.log a|))*
        ((ny:ℝ)*simpleKernelConstant*(1+|Real.log b|)) := by
  refine ⟨(shiftedTwoPhaseKernel_continuous ha hb α β).continuousOn.integrableOn_compact
    (isCompact_Icc.prod isCompact_Icc), ?_⟩
  change (∫ x in Icc x₀ x₁ ×ˢ Icc y₀ y₁,
    shiftedPhaseKernel a α x.1 * shiftedPhaseKernel b β x.2 ∂volume.prod volume) ≤ _
  rw [setIntegral_prod_mul (μ := volume) (ν := volume)
    (shiftedPhaseKernel a α) (shiftedPhaseKernel b β) (Icc x₀ x₁) (Icc y₀ y₁)]
  have hxint := shifted_kernel_interval_integral ha ha1 α nx hx hlenx
  have hyint := shifted_kernel_interval_integral hb hb1 β ny hy hleny
  rw [intervalIntegral.integral_of_le hx, ← integral_Icc_eq_integral_Ioc] at hxint
  rw [intervalIntegral.integral_of_le hy, ← integral_Icc_eq_integral_Ioc] at hyint
  exact mul_le_mul hxint hyint
    (integral_nonneg (fun t => shiftedPhaseKernel_nonneg b β t))
    (by have := simpleKernelConstant_pos; positivity)

/-- Coarea is applied to an already differentiated nonnegative density.
Its real Jacobian has been paid in hratio and the actual phase map is
injective on S. The two periodic phase integrals are then charged once. -/
theorem injective_signed_coarea_le {S : Set (ℝ × ℝ)}
    (hS : MeasurableSet S) (f : (ℝ × ℝ) → (ℝ × ℝ))
    (f' : (ℝ × ℝ) → ((ℝ × ℝ) →L[ℝ] (ℝ × ℝ)))
    (hf' : ∀ x ∈ S, HasFDerivWithinAt f (f' x) S x) (hf : InjOn f S)
    (x₀ x₁ y₀ y₁ : ℝ) (himage : f '' S ⊆ Icc x₀ x₁ ×ˢ Icc y₀ y₁)
    (density : (ℝ × ℝ) → ℝ) (hd : ContinuousOn density S)
    {C a b : ℝ} (hC : 0 ≤ C) (ha : 0 < a) (ha1 : a ≤ 1)
    (hb : 0 < b) (hb1 : b ≤ 1) (α β : ℝ)
    (hd0 : ∀ x ∈ S, 0 ≤ density x)
    (hratio : ∀ x ∈ S, density x ≤ C*|(f' x).det|)
    (nx ny : ℕ) (hx : x₀ ≤ x₁) (hy : y₀ ≤ y₁)
    (hlenx : x₁ ≤ x₀+(nx:ℝ)*(2*Real.pi))
    (hleny : y₁ ≤ y₀+(ny:ℝ)*(2*Real.pi)) :
    IntegrableOn (fun x => density x * shiftedTwoPhaseKernel a b α β (f x)) S ∧
      (∫ x in S, density x * shiftedTwoPhaseKernel a b α β (f x)) ≤
        C * (((nx:ℝ)*simpleKernelConstant*(1+|Real.log a|))*
          ((ny:ℝ)*simpleKernelConstant*(1+|Real.log b|))) := by
  have hrectangle := shifted_two_kernel_rectangle ha ha1 hb hb1 α β nx ny
    hx hy hlenx hleny
  have hcoarea := injective_weighted_coarea_le hS f f' hf' hf himage density
    (shiftedTwoPhaseKernel a b α β) hd
    (shiftedTwoPhaseKernel_continuous ha hb α β)
    (shiftedTwoPhaseKernel_nonneg a b α β) hrectangle.1 hC hd0 hratio
  exact ⟨hcoarea.1, hcoarea.2.trans (mul_le_mul_of_nonneg_left hrectangle.2 hC)⟩

end
end IsingBulk.HT.Lie
