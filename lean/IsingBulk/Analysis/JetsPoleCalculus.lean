import IsingBulk.Analysis.JetsRegularField

/-! Exact differentiation of an explicitly recorded selected pole. The
analytic numerator is extended through the diagonal; equality to the
singular coefficient is asserted only off that diagonal. -/
namespace IsingBulk.Jets
noncomputable section
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem one_pole_fderiv (r : E → ℂ) (δ : E →L[ℂ] ℂ) (x e : E)
    (hr : DifferentiableAt ℂ r x) (hd : δ x ≠ 0) :
    fderiv ℂ (fun y => r y/δ y) x e =
      (δ x*fderiv ℂ r x e-r x*δ e)/(δ x)^2 := by
  have hi := (hasFDerivAt_inv' (𝕜 := ℂ) hd).comp x δ.hasFDerivAt
  have hh := (hr.hasFDerivAt.fun_mul hi).fderiv
  change fderiv ℂ (fun y => r y*(δ y)⁻¹) x = _ at hh
  change fderiv ℂ (fun y => r y*(δ y)⁻¹) x e = _
  rw [hh]
  simp only [add_apply, smul_apply, smul_eq_mul, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.mulLeftRight_apply, neg_apply, Function.comp_apply]
  field_simp
  ring

def poleDerivativeNumerator (r : E → ℂ) (δ : E →L[ℂ] ℂ) (e : E) (x : E) : ℂ :=
  δ x*fderiv ℂ r x e-r x*δ e

theorem poleDerivativeNumerator_analytic (r : E → ℂ) (δ : E →L[ℂ] ℂ) (x e : E)
    (hr : AnalyticAt ℂ r x) : AnalyticAt ℂ (poleDerivativeNumerator r δ e) x := by
  have he : AnalyticAt ℂ (fun y => fderiv ℂ r y e) x := by
    exact ((ContinuousLinearMap.apply ℂ ℂ e).analyticAt (fderiv ℂ r x)).comp hr.fderiv
  exact ((δ.analyticAt x).mul he).sub (hr.mul analyticAt_const)

/-- A proved local equality transfers the quotient calculation to the
actual coefficient. This lemma alone makes no geometric or field claim. -/
theorem one_pole_local_derivative (f r : E → ℂ) (δ : E →L[ℂ] ℂ) (x e : E)
    (hr : AnalyticAt ℂ r x) (hd : δ x ≠ 0)
    (he : f =ᶠ[𝓝 x] fun y => r y/δ y) :
    fderiv ℂ f x e = poleDerivativeNumerator r δ e x/(δ x)^2 := by
  rw [he.fderiv_eq]
  exact one_pole_fderiv r δ x e hr.differentiableAt hd

def selectedDifferenceCLM {N : ℕ} (p q : Fin N) : (ℂ × (Fin N → ℂ)) →L[ℂ] ℂ :=
  (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) q)-
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) p)) :
    (Fin N → ℂ) →L[ℂ] ℂ).comp
    (ContinuousLinearMap.snd ℂ ℂ (Fin N → ℂ))

def spatialDirection {N : ℕ} (i : Fin N) : ℂ × (Fin N → ℂ) := (0, Pi.single i 1)

def residualDivergence {N : ℕ} (p q : Fin N) (z : ℂ × (Fin N → ℂ)) : ℂ :=
  ∑ i, fderiv ℂ (fun t : ℂ × (Fin N → ℂ) => regularResidualField p q t.1 t.2 i) z
    (spatialDirection i)

def divergenceRegularNumerator {N : ℕ} (p q : Fin N) (z : ℂ × (Fin N → ℂ)) : ℂ :=
  ∑ i, poleDerivativeNumerator (fun t : ℂ × (Fin N → ℂ) => residualRegularNumerator p q i t.1 t.2)
    (selectedDifferenceCLM p q) (spatialDirection i) z

/-- Actual residual divergence has two selected-difference factors at most.
The analytic/continuity assumptions hold on the neighborhood of the proved
base-point analytic formulas; none assumes a pole identity. -/
theorem residual_two_poles {N : ℕ} (p q : Fin N) (hpq : p ≠ q)
    (z : ℂ × (Fin N → ℂ))
    (hr : ∀ i, AnalyticAt ℂ
      (fun t : ℂ × (Fin N → ℂ) => residualRegularNumerator p q i t.1 t.2) z)
    (hcG : ContinuousAt (fun t : ℂ × (Fin N → ℂ) =>
      regularG t.1 (t.2 p)+regularG t.1 (t.2 q)) z)
    (hcD : ContinuousAt (fun t : ℂ × (Fin N → ℂ) =>
      selectedDenominator t.1 (t.2 p) (t.2 q)) z)
    (hp : Complex.sin (z.2 p) ≠ 0) (hq : Complex.sin (z.2 q) ≠ 0)
    (hd : z.2 q-z.2 p ≠ 0) (hg : regularG z.1 (z.2 p)+regularG z.1 (z.2 q) ≠ 0)
    (hD : selectedDenominator z.1 (z.2 p) (z.2 q) ≠ 0) :
    residualDivergence p q z = divergenceRegularNumerator p q z/(z.2 q-z.2 p)^2 ∧
      AnalyticAt ℂ (divergenceRegularNumerator p q) z := by
  have hcp : ContinuousAt (fun t : ℂ × (Fin N → ℂ) => Complex.sin (t.2 p)) z := by fun_prop
  have hcq : ContinuousAt (fun t : ℂ × (Fin N → ℂ) => Complex.sin (t.2 q)) z := by fun_prop
  have hed := (selectedDifferenceCLM p q).continuous.continuousAt.eventually_ne hd
  have he : ∀ i, (fun t : ℂ × (Fin N → ℂ) => regularResidualField p q t.1 t.2 i) =ᶠ[𝓝 z]
      (fun t => residualRegularNumerator p q i t.1 t.2 / selectedDifferenceCLM p q t) := by
    intro i
    filter_upwards [hcp.eventually_ne hp, hcq.eventually_ne hq, hed,
      hcG.eventually_ne hg, hcD.eventually_ne hD] with t htp htq htd htG htD
    exact residual_one_pole p q i hpq t.1 t.2 htp htq htd htG htD
  constructor
  · unfold residualDivergence divergenceRegularNumerator
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    exact one_pole_local_derivative _ _ (selectedDifferenceCLM p q) z (spatialDirection i)
      (hr i) hd (he i)
  · exact Finset.analyticAt_fun_sum _ fun i _ =>
      poleDerivativeNumerator_analytic _ _ z _ (hr i)

/-- The derivative direction above is exactly the fixed-parameter spatial
partial derivative, not a derivative in s. -/
theorem joint_spatial_eq {N : ℕ} (f : ℂ × (Fin N → ℂ) → ℂ)
    (s : ℂ) (φ : Fin N → ℂ) (i : Fin N) (hf : DifferentiableAt ℂ f (s,φ)) :
    fderiv ℂ f (s,φ) (spatialDirection i) =
      fderiv ℂ (fun ψ => f (s,ψ)) φ (Pi.single i 1) := by
  have hh := (hf.hasFDerivAt.comp φ
    ((hasFDerivAt_const s φ).prodMk (hasFDerivAt_id φ))).fderiv
  change fderiv ℂ (fun ψ => f (s,ψ)) φ = _ at hh
  rw [hh]
  rfl

end
end IsingBulk.Jets
