import IsingBulk.Analysis.JetsTerms

/-! The coefficient updates are the actual derivatives and field products
of the source operation. Their selected poles are certified by construction. -/
namespace IsingBulk.Jets
noncomputable section
open scoped Topology
open IsingBulk.Branch

def coefficientAction {N : ℕ} (p q : Fin N) (a : JetAction N)
    (C : ℂ × (Fin N → ℂ) → ℂ) (z : ℂ × (Fin N → ℂ)) : ℂ :=
  match a with
  | .coefficientParameter => fderiv ℂ C z (1,0)
  | .coefficientSpatial i => regularResidualField p q z.1 z.2 i*fderiv ℂ C z (spatialDirection i)
  | .divergence => residualDivergence p q z*C z
  | .numeratorSpatial i => regularResidualField p q z.1 z.2 i*C z
  | .numeratorParameter => C z
  | .cutoffSpatial i => -regularSelectedField p q z.1 z.2 i*C z

theorem SourceJetTerm.child_coefficient {N : ℕ} (T : SourceJetTerm N) (p q : Fin N)
    (hpq : p ≠ q) (a : JetAction N) (z : ℂ × (Fin N → ℂ))
    (hT : AnalyticAt ℂ T.regularPart z)
    (hB : ∀ i, AnalyticAt ℂ (fun t : ℂ × (Fin N → ℂ) => residualRegularNumerator p q i t.1 t.2) z)
    (hcG : ContinuousAt (fun t : ℂ × (Fin N → ℂ) => regularG t.1 (t.2 p)+regularG t.1 (t.2 q)) z)
    (hcD : ContinuousAt (fun t : ℂ × (Fin N → ℂ) => selectedDenominator t.1 (t.2 p) (t.2 q)) z)
    (hp : Complex.sin (z.2 p) ≠ 0) (hq : Complex.sin (z.2 q) ≠ 0)
    (hd : z.2 q-z.2 p ≠ 0) (hg : regularG z.1 (z.2 p)+regularG z.1 (z.2 q) ≠ 0)
    (hD : selectedDenominator z.1 (z.2 p) (z.2 q) ≠ 0) :
    (T.child p q a).coefficient p q z = coefficientAction p q a (T.coefficient p q) z := by
  have hd' : selectedDifferenceCLM p q z ≠ 0 := hd
  have hV := fun i => field_one_pole p q i z.1 z.2 hp hq hd hg hD
  have hR := fun i => residual_one_pole p q i hpq z.1 z.2 hp hq hd hg hD
  have hdiv := (residual_two_poles p q hpq z hB hcG hcD hp hq hd hg hD).1
  cases a with
  | coefficientParameter =>
    exact (pole_power_fderiv_fixed T.pole T.regularPart (selectedDifferenceCLM p q) z
      (1,0) hT.differentiableAt hd' (selectedDifference_parameter p q)).symm
  | coefficientSpatial i =>
    have hder : fderiv ℂ (T.coefficient p q) z (spatialDirection i) =
        poleJetNumerator T.pole T.regularPart (selectedDifferenceCLM p q) (spatialDirection i) z /
          (selectedDifferenceCLM p q z)^(T.pole+1) :=
      pole_power_fderiv T.pole T.regularPart _ z _ hT.differentiableAt hd'
    simp only [SourceJetTerm.child, SourceJetTerm.coefficient, coefficientAction]
    rw [hder, hR i]
    change _/selectedDifferenceCLM p q z^(T.pole+2) =
      (_/selectedDifferenceCLM p q z)*(_/selectedDifferenceCLM p q z^(T.pole+1))
    simp only [pow_add, pow_one, pow_two]
    field_simp
  | divergence =>
    simp only [SourceJetTerm.child, SourceJetTerm.coefficient, coefficientAction, hdiv]
    change _/selectedDifferenceCLM p q z^(T.pole+2) =
      (_/selectedDifferenceCLM p q z^2)*(_/selectedDifferenceCLM p q z^T.pole)
    rw [pow_add]
    field_simp
  | numeratorSpatial i =>
    simp only [SourceJetTerm.child, SourceJetTerm.coefficient, coefficientAction, hR i]
    change _/selectedDifferenceCLM p q z^(T.pole+1) =
      (_/selectedDifferenceCLM p q z)*(_/selectedDifferenceCLM p q z^T.pole)
    rw [pow_succ]
    field_simp
  | numeratorParameter => rfl
  | cutoffSpatial i =>
    simp only [SourceJetTerm.child, SourceJetTerm.coefficient, coefficientAction, hV i]
    change _/selectedDifferenceCLM p q z^(T.pole+1) =
      -(_/selectedDifferenceCLM p q z)*(_/selectedDifferenceCLM p q z^T.pole)
    rw [pow_succ]
    field_simp

theorem joint_parameter_eq {N : ℕ} (f : ℂ × (Fin N → ℂ) → ℂ)
    (z : ℂ × (Fin N → ℂ)) (hf : DifferentiableAt ℂ f z) :
    fderiv ℂ f z (1,0) = deriv (fun t => f (t,z.2)) z.1 := by
  have hh := hf.hasFDerivAt.comp_hasDerivAt z.1
    ((hasDerivAt_id z.1).prodMk (hasDerivAt_const z.1 z.2))
  convert! hh.deriv.symm using 1

def SourceJetTerm.stepValue {N : ℕ} (T : SourceJetTerm N) (p q : Fin N)
    (w : (Fin N → ℝ) → ℝ) (Q : ℂ × (Fin N → ℂ) → ℂ)
    (x : Fin N → ℝ) (z : ℂ × (Fin N → ℂ)) : ℂ :=
  (cutoffJet T.cutoff w x:ℂ) * regularDensityStep p q (T.density p q Q) z.1 z.2 -
    (∑ i, regularSelectedField p q z.1 z.2 i * (cutoffJet (i::T.cutoff) w x:ℂ)) *
      T.density p q Q z.1 z.2

theorem sum_actions {N : ℕ} (f : JetAction N → ℂ) :
    ((actions N).map f).sum = f .coefficientParameter + f .divergence + f .numeratorParameter +
      (∑ i, f (.coefficientSpatial i)) + (∑ i, f (.numeratorSpatial i)) +
        ∑ i, f (.cutoffSpatial i) := by
  simp [actions, Function.comp_def, List.finRange, List.sum_ofFn, add_assoc]

theorem SourceJetTerm.stepValue_eq_children {N : ℕ} (T : SourceJetTerm N) (p q : Fin N)
    (hpq : p ≠ q) (w : (Fin N → ℝ) → ℝ) (Q : ℂ × (Fin N → ℂ) → ℂ)
    (x : Fin N → ℝ) (z : ℂ × (Fin N → ℂ))
    (hT : AnalyticAt ℂ T.regularPart z) (hQ : AnalyticAt ℂ Q z)
    (hB : ∀ i, AnalyticAt ℂ (fun t : ℂ × (Fin N → ℂ) => residualRegularNumerator p q i t.1 t.2) z)
    (hcG : ContinuousAt (fun t : ℂ × (Fin N → ℂ) => regularG t.1 (t.2 p)+regularG t.1 (t.2 q)) z)
    (hcD : ContinuousAt (fun t : ℂ × (Fin N → ℂ) => selectedDenominator t.1 (t.2 p) (t.2 q)) z)
    (hs : z.1 ≠ 0)
    (hslit : ∀ i, 1-(z.1+z.1⁻¹-Complex.cos (z.2 i))^2 ∈ Complex.slitPlane)
    (hyd : ∀ i, 1-(regularY z.1 (z.2 i))^(-2:ℤ) ≠ 0)
    (hG : ∀ i, regularG z.1 (z.2 i) ≠ 0) (hn : ∀ i, Complex.sin (z.2 i) ≠ 0)
    (hbpq : regularB z.1 (z.2 p)-regularB z.1 (z.2 q) ≠ 0)
    (hd : z.2 q-z.2 p ≠ 0) (hg : regularG z.1 (z.2 p)+regularG z.1 (z.2 q) ≠ 0)
    (hD : selectedDenominator z.1 (z.2 p) (z.2 q) ≠ 0) (hK : regularKernel z.1 z.2 ≠ 0) :
    T.stepValue p q w Q x z =
      ((actions N).map (fun a => (T.child p q a).value p q w Q x z)).sum := by
  have hC : AnalyticAt ℂ (T.coefficient p q) z :=
    hT.div (((selectedDifferenceCLM p q).analyticAt z).pow T.pole) (pow_ne_zero T.pole hd)
  have hJ := directionJet_analytic numeratorDirection T.numerator Q z hQ
  have he := regularDensityStep_coefficient_numerator p q
    (fun s φ => T.coefficient p q (s,φ)) (fun s φ => numeratorJet T.numerator Q (s,φ)) z.1 z.2
    hC.differentiableAt hJ.differentiableAt hs hslit hyd hG hn hbpq hK
  change regularDensityStep p q (T.density p q Q) z.1 z.2 = _ at he
  have hc := fun a => T.child_coefficient p q hpq a z hT hB hcG hcD (hn p) (hn q) hd hg hD
  rw [sum_actions]
  simp only [SourceJetTerm.value, SourceJetTerm.density, hc]
  simp only [SourceJetTerm.child, coefficientAction, numeratorJet, directionJet,
    numeratorDirection, cutoffJet]
  rw [SourceJetTerm.stepValue, he]
  simp_rw [joint_parameter_eq _ z hC.differentiableAt,
    joint_parameter_eq _ z hJ.differentiableAt,
    joint_spatial_eq _ z.1 z.2 _ hC.differentiableAt,
    joint_spatial_eq _ z.1 z.2 _ hJ.differentiableAt]
  simp only [SourceJetTerm.density, numeratorJet, cutoffJet]
  simp only [add_div, Finset.sum_div, Finset.mul_sum, Finset.sum_mul, mul_add, sub_eq_add_neg,
    ← Finset.sum_neg_distrib]
  ring_nf
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

end
end IsingBulk.Jets
