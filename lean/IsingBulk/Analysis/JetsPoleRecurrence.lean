import IsingBulk.Analysis.JetsPoleCalculus

/-! Differentiation of the recorded selected pole at arbitrary finite order.
All equalities to quotients are restricted to a nonzero denominator. -/
namespace IsingBulk.Jets
noncomputable section
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def poleJetNumerator (m : ℕ) (r : E → ℂ) (δ : E →L[ℂ] ℂ) (e x : E) : ℂ :=
  δ x * fderiv ℂ r x e - (m : ℂ) * r x * δ e

theorem poleJetNumerator_analytic (m : ℕ) (r : E → ℂ) (δ : E →L[ℂ] ℂ)
    (x e : E) (hr : AnalyticAt ℂ r x) :
    AnalyticAt ℂ (poleJetNumerator m r δ e) x := by
  have he : AnalyticAt ℂ (fun y => fderiv ℂ r y e) x :=
    ((ContinuousLinearMap.apply ℂ ℂ e).analyticAt (fderiv ℂ r x)).comp hr.fderiv
  exact ((δ.analyticAt x).mul he).sub ((analyticAt_const.mul hr).mul analyticAt_const)

theorem pole_power_fderiv (m : ℕ) (r : E → ℂ) (δ : E →L[ℂ] ℂ) (x e : E)
    (hr : DifferentiableAt ℂ r x) (hd : δ x ≠ 0) :
    fderiv ℂ (fun y => r y/(δ y)^m) x e =
      poleJetNumerator m r δ e x / (δ x)^(m+1) := by
  cases m with
  | zero => simp [poleJetNumerator, hd]
  | succ m =>
    have hi := (hasFDerivAt_inv' (𝕜 := ℂ) (pow_ne_zero (m+1) hd)).comp x
      (δ.hasFDerivAt.pow (m+1))
    have hh := (hr.hasFDerivAt.fun_mul hi).fderiv
    change fderiv ℂ (fun y => r y*((δ y)^(m+1))⁻¹) x = _ at hh
    change fderiv ℂ (fun y => r y*((δ y)^(m+1))⁻¹) x e = _
    rw [hh]
    simp only [add_apply, smul_apply, smul_eq_mul, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.mulLeftRight_apply, neg_apply, Function.comp_apply,
      Nat.add_sub_cancel, poleJetNumerator]
    simp only [pow_succ]
    field_simp
    push_cast
    ring

/-- A derivative in a direction that fixes the selected difference does not
increase the pole order. This applies to the source parameter derivative. -/
theorem pole_power_fderiv_fixed (m : ℕ) (r : E → ℂ) (δ : E →L[ℂ] ℂ) (x e : E)
    (hr : DifferentiableAt ℂ r x) (hd : δ x ≠ 0) (he : δ e = 0) :
    fderiv ℂ (fun y => r y/(δ y)^m) x e = fderiv ℂ r x e/(δ x)^m := by
  rw [pole_power_fderiv m r δ x e hr hd]
  simp only [poleJetNumerator, he, mul_zero, sub_zero, pow_succ]
  field_simp

theorem pole_power_local_derivative (m : ℕ) (f r : E → ℂ) (δ : E →L[ℂ] ℂ)
    (x e : E) (hr : AnalyticAt ℂ r x) (hd : δ x ≠ 0)
    (he : f =ᶠ[𝓝 x] fun y => r y/(δ y)^m) :
    fderiv ℂ f x e = poleJetNumerator m r δ e x/(δ x)^(m+1) := by
  rw [he.fderiv_eq]
  exact pole_power_fderiv m r δ x e hr.differentiableAt hd

theorem selectedDifference_parameter {N : ℕ} (p q : Fin N) :
    selectedDifferenceCLM p q (1,0) = 0 := by
  simp [selectedDifferenceCLM]

end
end IsingBulk.Jets
