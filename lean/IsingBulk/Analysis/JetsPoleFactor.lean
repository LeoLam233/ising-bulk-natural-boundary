import IsingBulk.Analysis.RegularPair
import IsingBulk.Analysis.SelectedField

/-! Source selected-difference factorization from the explicit inverse
dispersion relation. No general divided-difference analyticity is assumed. -/
namespace IsingBulk.Jets
noncomputable section
open IsingBulk.Branch
open scoped Topology
attribute [local fun_prop] analyticAt_fst analyticAt_snd

def regularG (s φ : ℂ) : ℂ := Complex.I*(regularY s φ-(regularY s φ)⁻¹)/2

def sineQuotient (φ : ℂ) : ℂ := 2*halfSineQuotient (2*φ)

/-- beta is the scalar even analytic numerator of b, not the residual field. -/
def regularBeta (s φ : ℂ) : ℂ := regularG s φ / sineQuotient φ

def regularB (s φ : ℂ) : ℂ := regularG s φ / Complex.sin φ

def selectedDenominator (s p q : ℂ) : ℂ :=
  2*regularG s p*Complex.cos ((p+q)/2)*halfSineQuotient (q-p) +
  2*Complex.sin ((p+q)/2)*halfSineQuotient (p-q)*Complex.sin p*
    (2*(s+s⁻¹)-Complex.cos p-Complex.cos q)/(regularG s p+regularG s q)

def selectedRegularFactor (s p q : ℂ) : ℂ :=
  regularG s p * regularG s q / selectedDenominator s p q

theorem regularG_even (s φ : ℂ) : regularG s (-φ) = regularG s φ := by
  simp [regularG, regularY_even]

theorem mul_sineQuotient (φ : ℂ) : φ*sineQuotient φ = Complex.sin φ := by
  have h := mul_halfSineQuotient (2*φ)
  simpa [sineQuotient, mul_assoc, mul_left_comm] using h

theorem sineQuotient_zero : sineQuotient 0 = 1 := by
  simp [sineQuotient, halfSineQuotient_zero]

theorem sineQuotient_even (φ : ℂ) : sineQuotient (-φ) = sineQuotient φ := by
  by_cases h : φ = 0
  · simp [h]
  · have h1 := mul_sineQuotient (-φ)
    have h2 := mul_sineQuotient φ
    rw [Complex.sin_neg] at h1
    apply (mul_left_inj' h).mp
    linear_combination -h1 - h2

theorem regularBeta_even (s φ : ℂ) : regularBeta s (-φ) = regularBeta s φ := by
  simp [regularBeta, regularG_even, sineQuotient_even]

theorem regularB_eq_beta_div (s φ : ℂ) : regularB s φ = regularBeta s φ / φ := by
  rw [regularB, regularBeta, div_div, mul_comm (sineQuotient φ) φ, mul_sineQuotient]

theorem regularG_sq (s φ : ℂ) :
    (regularG s φ)^2 = 1-(s+s⁻¹-Complex.cos φ)^2 := by
  have hd := dispersion_regularY s φ
  unfold dispersion at hd
  have hy : s+s⁻¹-Complex.cos φ = (regularY s φ+(regularY s φ)⁻¹)/2 := by
    linear_combination hd
  rw [hy]
  unfold regularG
  field_simp [regularY_ne_zero]
  ring_nf
  simp [Complex.I_sq]
  ring

theorem regularG_difference (s p q : ℂ) (h : regularG s p+regularG s q ≠ 0) :
    regularG s p-regularG s q = (Complex.cos p-Complex.cos q)*
      (2*(s+s⁻¹)-Complex.cos p-Complex.cos q)/(regularG s p+regularG s q) := by
  apply (eq_div_iff h).mpr
  linear_combination regularG_sq s p - regularG_sq s q

theorem selected_denominator_identity (s p q : ℂ) (hg : regularG s p+regularG s q ≠ 0) :
    regularG s p*Complex.sin q-regularG s q*Complex.sin p =
      (q-p)*selectedDenominator s p q := by
  rw [show regularG s p*Complex.sin q-regularG s q*Complex.sin p =
    regularG s p*(Complex.sin q-Complex.sin p)+(regularG s p-regularG s q)*Complex.sin p by ring,
    Complex.sin_sub_sin, regularG_difference s p q hg, Complex.cos_sub_cos]
  rw [← mul_halfSineQuotient (q-p), ← mul_halfSineQuotient (p-q)]
  simp only [show q+p = p+q by ring]
  unfold selectedDenominator
  ring

theorem selected_difference_pole (s p q : ℂ) (hp : Complex.sin p ≠ 0)
    (hq : Complex.sin q ≠ 0) (hδ : q-p ≠ 0)
    (hg : regularG s p+regularG s q ≠ 0) (hD : selectedDenominator s p q ≠ 0) :
    regularB s p*regularB s q/(regularB s p-regularB s q) =
      selectedRegularFactor s p q/(q-p) := by
  have hd : regularG s p*Complex.sin q-regularG s q*Complex.sin p ≠ 0 := by
    rw [selected_denominator_identity s p q hg]
    exact mul_ne_zero hδ hD
  rw [regularB, regularB, residual_denominator _ _ _ _ hp hq hd,
    selected_denominator_identity s p q hg]
  unfold selectedRegularFactor
  field_simp

theorem regularG_base_ne_zero (s : ℂ) (c : ℝ)
    (hS : s+s⁻¹ = (1+c:ℂ)) (hc : |c| < 1) : regularG s 0 ≠ 0 := by
  intro h
  have hd := regularY_base_denominator s c hS hc
  have he : regularY s 0 = (regularY s 0)⁻¹ := by
    unfold regularG at h
    have hz : regularY s 0-(regularY s 0)⁻¹ = 0 := by
      simpa using h
    exact sub_eq_zero.mp hz
  apply hd
  have hy := mul_inv_cancel₀ (regularY_ne_zero s 0)
  rw [← he] at hy
  simp [hy]

theorem selectedDenominator_base (s : ℂ) : selectedDenominator s 0 0 = regularG s 0 := by
  simp [selectedDenominator, halfSineQuotient_zero]
  ring

theorem regularG_analytic_base (s : ℂ) (c : ℝ) (hs : s ≠ 0)
    (hS : s+s⁻¹ = (1+c:ℂ)) (hc : |c| < 1) :
    AnalyticAt ℂ (fun z : ℂ × ℂ => regularG z.1 z.2) (s,0) := by
  have hy := regularY_analytic_base s c hs hS hc
  exact (analyticAt_const.mul (hy.sub (hy.inv (regularY_ne_zero s 0)))).div_const

theorem sineQuotient_analytic : AnalyticAt ℂ sineQuotient 0 := by
  have h := AnalyticAt.comp_of_eq halfSineQuotient_analytic
    (show AnalyticAt ℂ (fun z : ℂ => 2*z) 0 by fun_prop) (by simp)
  exact analyticAt_const.mul h

theorem regularBeta_analytic_base (s : ℂ) (c : ℝ) (hs : s ≠ 0)
    (hS : s+s⁻¹ = (1+c:ℂ)) (hc : |c| < 1) :
    AnalyticAt ℂ (fun z : ℂ × ℂ => regularBeta z.1 z.2) (s,0) := by
  exact (regularG_analytic_base s c hs hS hc).div
    (AnalyticAt.comp (f := fun z : ℂ × ℂ => z.2) (g := sineQuotient)
      sineQuotient_analytic analyticAt_snd) (by simp [sineQuotient_zero])

theorem selectedDenominator_analytic_base (s : ℂ) (c : ℝ) (hs : s ≠ 0)
    (hS : s+s⁻¹ = (1+c:ℂ)) (hc : |c| < 1) :
    AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ => selectedDenominator z.1 z.2.1 z.2.2)
      (s,0,0) := by
  have hG := regularG_analytic_base s c hs hS hc
  have hp : AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ => regularG z.1 z.2.1) (s,0,0) :=
    AnalyticAt.comp (g := fun z : ℂ × ℂ => regularG z.1 z.2) (f := fun z : ℂ × ℂ × ℂ => (z.1,z.2.1)) hG (show AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ => (z.1,z.2.1)) (s,0,0) by fun_prop)
  have hq : AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ => regularG z.1 z.2.2) (s,0,0) :=
    AnalyticAt.comp (g := fun z : ℂ × ℂ => regularG z.1 z.2) (f := fun z : ℂ × ℂ × ℂ => (z.1,z.2.2)) hG (show AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ => (z.1,z.2.2)) (s,0,0) by fun_prop)
  have hpm : AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ => halfSineQuotient (z.2.1-z.2.2))
      (s,0,0) := AnalyticAt.comp_of_eq halfSineQuotient_analytic (by fun_prop) (by simp)
  have hmp : AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ => halfSineQuotient (z.2.2-z.2.1))
      (s,0,0) := AnalyticAt.comp_of_eq halfSineQuotient_analytic (by fun_prop) (by simp)
  have hsource : AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ =>
      2*(z.1+z.1⁻¹)-Complex.cos z.2.1-Complex.cos z.2.2) (s,0,0) := by
    fun_prop (disch := exact hs)
  have hne : regularG s 0+regularG s 0 ≠ 0 := by
    simpa [← two_mul] using mul_ne_zero (two_ne_zero : (2:ℂ) ≠ 0)
      (regularG_base_ne_zero s c hS hc)
  exact (((analyticAt_const.mul hp).mul (by fun_prop)).mul hmp).add
    (((((analyticAt_const.mul (by fun_prop)).mul hpm).mul (by fun_prop)).mul hsource).div
      (hp.add hq) hne)

theorem selectedRegularFactor_analytic_base (s : ℂ) (c : ℝ) (hs : s ≠ 0)
    (hS : s+s⁻¹ = (1+c:ℂ)) (hc : |c| < 1) :
    AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ => selectedRegularFactor z.1 z.2.1 z.2.2)
      (s,0,0) := by
  have hG := regularG_analytic_base s c hs hS hc
  have hp : AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ => regularG z.1 z.2.1) (s,0,0) :=
    AnalyticAt.comp (g := fun z : ℂ × ℂ => regularG z.1 z.2) (f := fun z : ℂ × ℂ × ℂ => (z.1,z.2.1)) hG (show AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ => (z.1,z.2.1)) (s,0,0) by fun_prop)
  have hq : AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ => regularG z.1 z.2.2) (s,0,0) :=
    AnalyticAt.comp (g := fun z : ℂ × ℂ => regularG z.1 z.2) (f := fun z : ℂ × ℂ × ℂ => (z.1,z.2.2)) hG (show AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ => (z.1,z.2.2)) (s,0,0) by fun_prop)
  exact (hp.mul hq).div (selectedDenominator_analytic_base s c hs hS hc)
    (by rw [selectedDenominator_base]; exact regularG_base_ne_zero s c hS hc)

/-- A single fixed neighborhood supplies all regular nonvanishing factors.
Its choice precedes the number of angular variables. -/
theorem selected_factors_eventually (s : ℂ) (c : ℝ) (hs : s ≠ 0)
    (hS : s+s⁻¹ = (1+c:ℂ)) (hc : |c| < 1) :
    ∀ᶠ z : ℂ × ℂ × ℂ in 𝓝 (s,0,0),
      regularBeta z.1 z.2.1 ≠ 0 ∧ regularBeta z.1 z.2.2 ≠ 0 ∧
      regularG z.1 z.2.1+regularG z.1 z.2.2 ≠ 0 ∧
      selectedDenominator z.1 z.2.1 z.2.2 ≠ 0 ∧
      AnalyticAt ℂ (fun t : ℂ × ℂ × ℂ => selectedRegularFactor t.1 t.2.1 t.2.2) z := by
  have hG := regularG_analytic_base s c hs hS hc
  have hβ := regularBeta_analytic_base s c hs hS hc
  have hgp : AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ => regularG z.1 z.2.1) (s,0,0) :=
    AnalyticAt.comp (g := fun z : ℂ × ℂ => regularG z.1 z.2) (f := fun z : ℂ × ℂ × ℂ => (z.1,z.2.1)) hG (show AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ => (z.1,z.2.1)) (s,0,0) by fun_prop)
  have hgq : AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ => regularG z.1 z.2.2) (s,0,0) :=
    AnalyticAt.comp (g := fun z : ℂ × ℂ => regularG z.1 z.2) (f := fun z : ℂ × ℂ × ℂ => (z.1,z.2.2)) hG (show AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ => (z.1,z.2.2)) (s,0,0) by fun_prop)
  have hbp : AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ => regularBeta z.1 z.2.1) (s,0,0) :=
    AnalyticAt.comp (g := fun z : ℂ × ℂ => regularBeta z.1 z.2) (f := fun z : ℂ × ℂ × ℂ => (z.1,z.2.1)) hβ (show AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ => (z.1,z.2.1)) (s,0,0) by fun_prop)
  have hbq : AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ => regularBeta z.1 z.2.2) (s,0,0) :=
    AnalyticAt.comp (g := fun z : ℂ × ℂ => regularBeta z.1 z.2) (f := fun z : ℂ × ℂ × ℂ => (z.1,z.2.2)) hβ (show AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ => (z.1,z.2.2)) (s,0,0) by fun_prop)
  have hβ0 : regularBeta s 0 ≠ 0 := by
    simpa [regularBeta, sineQuotient_zero] using regularG_base_ne_zero s c hS hc
  have hgg : regularG s 0+regularG s 0 ≠ 0 := by
    simpa [← two_mul] using mul_ne_zero (two_ne_zero : (2:ℂ) ≠ 0)
      (regularG_base_ne_zero s c hS hc)
  have hd := (selectedDenominator_analytic_base s c hs hS hc).continuousAt.eventually_ne
    (by rw [selectedDenominator_base]; exact regularG_base_ne_zero s c hS hc)
  exact (hbp.continuousAt.eventually_ne hβ0).and
    ((hbq.continuousAt.eventually_ne hβ0).and
      (((hgp.add hgq).continuousAt.eventually_ne hgg).and
        (hd.and (selectedRegularFactor_analytic_base s c hs hS hc).eventually_analyticAt)))

end
end IsingBulk.Jets


