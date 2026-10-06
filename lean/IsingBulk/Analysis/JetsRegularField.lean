import IsingBulk.Analysis.JetsSelected
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! Explicit regular numerators of the source selected field. All comparisons
with singular field values are restricted to the genuine regular locus. -/
namespace IsingBulk.Jets
noncomputable section
open scoped BigOperators Topology
open IsingBulk.Branch IsingBulk.Lie
attribute [local fun_prop] analyticAt_fst analyticAt_snd

def regularA (s φ : ℂ) : ℂ := sourceSPrime s / (-regularG s φ)

def aSum {N : ℕ} (s : ℂ) (φ : Fin N → ℂ) : ℂ := ∑ i, regularA s (φ i)

def regularSelectedField {N : ℕ} (p q : Fin N) (s : ℂ) (φ : Fin N → ℂ) : Fin N → ℂ :=
  selectedField (fun i => regularA s (φ i)) (fun i => regularB s (φ i)) p q

def regularResidualField {N : ℕ} (p q : Fin N) (s : ℂ) (φ : Fin N → ℂ) : Fin N → ℂ :=
  residualField (fun i => regularA s (φ i)) (fun i => regularB s (φ i)) p q

def fieldRegularNumerator {N : ℕ} (p q i : Fin N) (s : ℂ) (φ : Fin N → ℂ) : ℂ :=
  regularA s (φ i)*(φ q-φ p) +
    (if i = p then aSum s φ*regularG s (φ q)*Complex.sin (φ p)/
      selectedDenominator s (φ p) (φ q) else 0) -
    (if i = q then aSum s φ*regularG s (φ p)*Complex.sin (φ q)/
      selectedDenominator s (φ p) (φ q) else 0)

def residualRegularNumerator {N : ℕ} (p q i : Fin N) (s : ℂ) (φ : Fin N → ℂ) : ℂ :=
  (if i = p then -aSum s φ*selectedRegularFactor s (φ p) (φ q) else 0) +
  (if i = q then aSum s φ*selectedRegularFactor s (φ p) (φ q) else 0)

theorem regularA_chartPhase (s : ℂ) (v θ : ℝ) (u : ℂ)
    (hg : 0 < (angularG v θ u).re) :
    regularA s (chartPhase s v θ u) = chartA s v θ u := by
  rw [regularA, regularG_chartPhase s v θ u hg]
  rfl

theorem regularSelectedField_chart {n : ℕ} (p q : Fin (n+1)) (v θ : ℝ)
    (s : ℂ) (x : AngularSpace n) (hg : ∀ i, 0 < (angularG v θ (x i)).re) :
    regularSelectedField p q s (fun i => chartPhase s v θ (x i)) = actualField v θ p q s x := by
  simp only [regularSelectedField, actualField, regularA_chartPhase _ _ _ _ (hg _),
    regularB_chartPhase _ _ _ _ (hg _)]

theorem regularResidualField_chart {n : ℕ} (p q : Fin (n+1)) (v θ : ℝ)
    (s : ℂ) (x : AngularSpace n) (hs : s ≠ 0)
    (hr : ∀ i, 0 < (chartW s v θ (x i)).re)
    (hi : ∀ i, 0 < (chartW s v θ (x i)).im)
    (hg : ∀ i, 0 < (angularG v θ (x i)).re) :
    regularResidualField p q s (fun i => chartPhase s v θ (x i)) = actualResidual v θ p q s x := by
  rw [actualResidual_eq v θ p q s x hs hr hi
    (fun i h => by simpa [h] using hg i)]
  simp only [regularResidualField, regularA_chartPhase _ _ _ _ (hg _),
    regularB_chartPhase _ _ _ _ (hg _)]

theorem selected_ratios (s p q : ℂ) (hp : Complex.sin p ≠ 0)
    (hq : Complex.sin q ≠ 0) (hδ : q-p ≠ 0)
    (hg : regularG s p+regularG s q ≠ 0) (hD : selectedDenominator s p q ≠ 0) :
    regularB s q/(regularB s p-regularB s q) =
      (regularG s q*Complex.sin p/selectedDenominator s p q)/(q-p) ∧
    regularB s p/(regularB s p-regularB s q) =
      (regularG s p*Complex.sin q/selectedDenominator s p q)/(q-p) := by
  have hd : regularG s p*Complex.sin q-regularG s q*Complex.sin p ≠ 0 := by
    rw [selected_denominator_identity s p q hg]
    exact mul_ne_zero hδ hD
  have hdiff : regularB s p-regularB s q =
      (q-p)*selectedDenominator s p q/(Complex.sin p*Complex.sin q) := by
    unfold regularB
    rw [div_sub_div _ _ hp hq]
    congr 1
    simpa [mul_comm] using selected_denominator_identity s p q hg
  rw [hdiff]
  unfold regularB
  constructor <;> field_simp

theorem field_one_pole {N : ℕ} (p q i : Fin N) (s : ℂ) (φ : Fin N → ℂ)
    (hp : Complex.sin (φ p) ≠ 0) (hq : Complex.sin (φ q) ≠ 0)
    (hδ : φ q-φ p ≠ 0) (hg : regularG s (φ p)+regularG s (φ q) ≠ 0)
    (hD : selectedDenominator s (φ p) (φ q) ≠ 0) :
    regularSelectedField p q s φ i = fieldRegularNumerator p q i s φ/(φ q-φ p) := by
  have ht := selected_ratios s (φ p) (φ q) hp hq hδ hg hD
  unfold regularSelectedField selectedField fieldRegularNumerator aSum
  simp only [mul_div_assoc]
  rw [ht.1, ht.2]
  split_ifs <;> field_simp <;> ring

theorem residual_one_pole {N : ℕ} (p q i : Fin N) (hpq : p ≠ q) (s : ℂ) (φ : Fin N → ℂ)
    (hp : Complex.sin (φ p) ≠ 0) (hq : Complex.sin (φ q) ≠ 0)
    (hδ : φ q-φ p ≠ 0) (hg : regularG s (φ p)+regularG s (φ q) ≠ 0)
    (hD : selectedDenominator s (φ p) (φ q) ≠ 0) :
    regularResidualField p q s φ i = residualRegularNumerator p q i s φ/(φ q-φ p) := by
  unfold regularResidualField
  rw [residualField_two_entries _ _ p q hpq]
  have ht := selected_difference_pole s (φ p) (φ q) hp hq hδ hg hD
  unfold residualRegularNumerator aSum
  simp only [show ∀ a b c d : ℂ, a*b*c/d = a*(b*c/d) by intros; ring]
  rw [ht]
  split_ifs <;> ring

theorem regularA_analytic_base (s : ℂ) (c : ℝ) (hs : s ≠ 0)
    (hS : s+s⁻¹ = (1+c:ℂ)) (hc : |c| < 1) :
    AnalyticAt ℂ (fun z : ℂ × ℂ => regularA z.1 z.2) (s,0) := by
  apply AnalyticAt.div
  · unfold sourceSPrime
    exact analyticAt_const.sub ((analyticAt_fst.pow 2).inv (pow_ne_zero 2 hs))
  · exact (regularG_analytic_base s c hs hS hc).neg
  · exact neg_ne_zero.mpr (regularG_base_ne_zero s c hS hc)

theorem analytic_coordinate {N : ℕ} (i : Fin N) (z : ℂ × (Fin N → ℂ)) :
    AnalyticAt ℂ (fun t : ℂ × (Fin N → ℂ) => t.2 i) z :=
  ((ContinuousLinearMap.proj (R := ℂ) i).comp
    (ContinuousLinearMap.snd ℂ ℂ (Fin N → ℂ))).analyticAt z

attribute [local fun_prop] analytic_coordinate

/-- The regular numerator extends across the selected diagonal. This
analyticity assertion is distinct from the uniform coefficient-jet bound. -/
theorem field_numerators_analytic {N : ℕ} (p q i : Fin N) (s : ℂ) (c : ℝ)
    (hs : s ≠ 0) (hS : s+s⁻¹ = (1+c:ℂ)) (hc : |c| < 1) :
    AnalyticAt ℂ (fun z : ℂ × (Fin N → ℂ) => fieldRegularNumerator p q i z.1 z.2) (s,0) ∧
    AnalyticAt ℂ (fun z : ℂ × (Fin N → ℂ) => residualRegularNumerator p q i z.1 z.2) (s,0) := by
  have hA : ∀ k : Fin N, AnalyticAt ℂ
      (fun z : ℂ × (Fin N → ℂ) => regularA z.1 (z.2 k)) (s,0) := by
    intro k
    exact AnalyticAt.comp (g := fun z : ℂ × ℂ => regularA z.1 z.2)
      (f := fun z : ℂ × (Fin N → ℂ) => (z.1,z.2 k))
      (regularA_analytic_base s c hs hS hc) (analyticAt_fst.prod (analytic_coordinate k _))
  have hG : ∀ k : Fin N, AnalyticAt ℂ
      (fun z : ℂ × (Fin N → ℂ) => regularG z.1 (z.2 k)) (s,0) := by
    intro k
    exact AnalyticAt.comp (g := fun z : ℂ × ℂ => regularG z.1 z.2)
      (f := fun z : ℂ × (Fin N → ℂ) => (z.1,z.2 k))
      (regularG_analytic_base s c hs hS hc) (analyticAt_fst.prod (analytic_coordinate k _))
  have hsum : AnalyticAt ℂ (fun z : ℂ × (Fin N → ℂ) => aSum z.1 z.2) (s,0) :=
    Finset.analyticAt_fun_sum _ fun k _ => hA k
  have hmap : AnalyticAt ℂ
      (fun z : ℂ × (Fin N → ℂ) => (z.1,z.2 p,z.2 q)) (s,0) :=
    analyticAt_fst.prod ((analytic_coordinate p _).prod (analytic_coordinate q _))
  have hD : AnalyticAt ℂ (fun z : ℂ × (Fin N → ℂ) =>
      selectedDenominator z.1 (z.2 p) (z.2 q)) (s,0) :=
    AnalyticAt.comp (g := fun z : ℂ × ℂ × ℂ => selectedDenominator z.1 z.2.1 z.2.2)
      (f := fun z : ℂ × (Fin N → ℂ) => (z.1,z.2 p,z.2 q))
      (selectedDenominator_analytic_base s c hs hS hc) hmap
  have hH : AnalyticAt ℂ (fun z : ℂ × (Fin N → ℂ) =>
      selectedRegularFactor z.1 (z.2 p) (z.2 q)) (s,0) :=
    AnalyticAt.comp (g := fun z : ℂ × ℂ × ℂ => selectedRegularFactor z.1 z.2.1 z.2.2)
      (f := fun z : ℂ × (Fin N → ℂ) => (z.1,z.2 p,z.2 q))
      (selectedRegularFactor_analytic_base s c hs hS hc) hmap
  have hD0 : selectedDenominator s 0 0 ≠ 0 := by
    rw [selectedDenominator_base]; exact regularG_base_ne_zero s c hS hc
  have hsin : ∀ k : Fin N, AnalyticAt ℂ
      (fun z : ℂ × (Fin N → ℂ) => Complex.sin (z.2 k)) (s,0) := by
    intro k
    exact Complex.analyticAt_sin.comp (analytic_coordinate k _)
  constructor
  · unfold fieldRegularNumerator
    split_ifs <;> fun_prop (disch := exact hD0)
  · unfold residualRegularNumerator
    split_ifs <;> fun_prop

end
end IsingBulk.Jets
