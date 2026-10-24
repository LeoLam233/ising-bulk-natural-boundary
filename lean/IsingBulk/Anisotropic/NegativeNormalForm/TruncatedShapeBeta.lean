import IsingBulk.Anisotropic.NegativeNormalForm.WeightedShapeBeta

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open MeasureTheory Set IsingBulk.First IsingBulk.Anisotropic.NegativeDominance
open scoped BigOperators

def truncatedExponential (C L : ℝ) : ℝ → ℝ :=
  (Ioo 0 L).indicator (fun x => Real.exp (C*(Real.sqrt x+x))-1)

theorem truncatedExponential_measurable (C L : ℝ) : Measurable (truncatedExponential C L) :=
  (by fun_prop : Continuous (fun x : ℝ => Real.exp (C*(Real.sqrt x+x))-1)).measurable.indicator measurableSet_Ioo

theorem truncatedExponential_nonneg (C L x : ℝ) (hC : 0≤C) : 0≤truncatedExponential C L x := by
  unfold truncatedExponential
  by_cases hx : x∈Ioo 0 L
  · rw [indicator_of_mem hx]
    have hx0 := hx.1
    exact sub_nonneg.mpr (Real.one_le_exp (by positivity))
  · simp [indicator_of_notMem hx]

theorem truncatedExponential_norm_bound (C L x : ℝ) (hC : 0≤C) :
    ‖truncatedExponential C L x‖≤Real.exp (C*(Real.sqrt L+L)) := by
  rw [Real.norm_eq_abs,abs_of_nonneg (truncatedExponential_nonneg C L x hC)]
  unfold truncatedExponential
  by_cases hx : x∈Ioo 0 L
  · rw [indicator_of_mem hx]
    have he : Real.exp (C*(Real.sqrt x+x))≤Real.exp (C*(Real.sqrt L+L)) := by
      gcongr
      exact hx.2.le
      exact hx.2.le
    linarith
  · rw [indicator_of_notMem hx]
    exact (Real.exp_pos _).le

theorem truncatedExponential_beta_integral (a j : ℕ) (C L : ℝ) :
    (∫ x in Ioi (0:ℝ),truncatedExponential C L x*(x^(a-1)/(1+x)^(j+1)))=
      ∫ x in Ioo (0:ℝ) L,(Real.exp (C*(Real.sqrt x+x))-1)*(x^(a-1)/(1+x)^(j+1)) := by
  unfold truncatedExponential
  simp_rw [←indicator_mul_left (Ioo 0 L) (fun x : ℝ => Real.exp (C*(Real.sqrt x+x))-1)
    (fun x : ℝ => x^(a-1)/(1+x)^(j+1))]
  rw [integral_indicator measurableSet_Ioo,Measure.restrict_restrict measurableSet_Ioo]
  rw [inter_eq_left.mpr Ioo_subset_Ioi_self]

theorem truncatedShapeBeta_integrable {n : ℕ} (ho : Odd (n+1)) (hn : 2≤n)
    (j : ℕ) (hj : alpha (n+1)≤j) (tau c : ℝ) (ht : 0<tau) (hc : 0<c)
    (C L : ℝ) (hC : 0≤C) :
    Integrable (fun q : Fin n→ℝ => truncatedExponential C L
      (c*(∑ i : Fin (n+1),shapeExtend q i^2)/tau)*constrainedBetaKernel n j tau c q) := by
  have hm : AEStronglyMeasurable (fun q : Fin n→ℝ => truncatedExponential C L
      (c*(∑ i : Fin (n+1),shapeExtend q i^2)/tau)) := by
    apply Measurable.aestronglyMeasurable
    apply (truncatedExponential_measurable C L).comp
    unfold shapeExtend
    fun_prop
  have hk := constrainedBetaKernel_integrable ho hn j hj tau c ht hc
  apply Integrable.mono' (hk.const_mul (Real.exp (C*(Real.sqrt L+L)))) (hm.mul hk.aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro q
  change ‖truncatedExponential C L _ * constrainedBetaKernel n j tau c q‖≤_
  rw [norm_mul,Real.norm_of_nonneg (constrainedBetaKernel_nonneg n j ht.le hc.le q)]
  exact mul_le_mul_of_nonneg_right (truncatedExponential_norm_bound C L _ hC)
    (constrainedBetaKernel_nonneg n j ht.le hc.le q)

theorem truncatedShapeBeta_error {n : ℕ} (ho : Odd (n+1)) (hn : 2≤n)
    (j K : ℕ) (hj : 4*alpha (n+1)+4≤j) (hKj : K≤j-j/2)
    (tau c C L : ℝ) (ht : 0<tau) (hc : 0<c) (hC : 0≤C) (hL : 1≤L)
    (hK : C*(Real.sqrt L+L)≤(K:ℝ)*Real.log 2) :
    (∫ q : Fin n→ℝ,truncatedExponential C L (c*(∑ i : Fin (n+1),shapeExtend q i^2)/tau)*
      constrainedBetaKernel n j tau c q)/constrainedBetaValue (n+1) j tau c≤
      expErrorConstant C 1*(Real.sqrt ((alpha (n+1):ℝ)/((j:ℝ)-alpha (n+1)))+
        (alpha (n+1):ℝ)/((j:ℝ)-alpha (n+1)))+(2:ℝ)^(-((j-K-j/2:ℕ):ℤ))*4^alpha (n+1) := by
  rw [weightedShapeBeta_normalized ho hn j (by omega) tau c ht hc,truncatedExponential_beta_integral]
  have ha : 0<alpha (n+1) := by
    rw [alpha_eq_derivativeOrder]
    exact IsingBulk.HT.First.derivativeOrder_pos ho (by omega)
  exact beta_exponential_truncated _ j K ha hj hKj C L hC hL hK

end
end IsingBulk.Anisotropic.NegativeNormalForm
