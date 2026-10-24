import IsingBulk.Anisotropic.NegativeNormalForm.DensityResidueScalar
import Mathlib.Analysis.SpecialFunctions.Log.Summable

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open Set Metric Filter
open scoped Topology BigOperators

/-- The actual ratio of any nonvanishing analytic scalar factor is Lipschitz
relative to its moving center, with the radius chosen before the dimension. -/
theorem analytic_parameter_ratio_control (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0)
    (hf0 : f 0≠0) :
    ∃ r L : ℝ, 0<r ∧ 0<L ∧ ∀ t t₀ : ℂ, ‖t‖<r → ‖t₀‖<r →
      f t₀≠0 ∧ ‖f t/f t₀-1‖≤L*‖t-t₀‖ := by
  have ha : AnalyticAt ℂ (fun p : ℂ × ℂ => f p.1/f p.2) 0 :=
    (hf.fun_comp_of_eq (f := fun p : ℂ × ℂ => p.1) analyticAt_fst rfl).div
      (hf.fun_comp_of_eq (f := fun p : ℂ × ℂ => p.2) analyticAt_snd rfl) hf0
  obtain ⟨r,L,hr,hL,_ha,hLip⟩ := analytic_uniform_lipschitz ha
  obtain ⟨s,hs,hball⟩ := Metric.mem_nhds_iff.mp (hf.continuousAt.eventually_ne hf0)
  refine ⟨min r s,L,lt_min hr hs,hL,?_⟩
  intro t t₀ ht ht₀
  have hn : f t₀≠0 := hball (by simpa using ht₀.trans_le (min_le_right _ _))
  refine ⟨hn,?_⟩
  have hp : ‖(t,t₀)‖<r := (max_lt ht ht₀).trans_le (min_le_left _ _)
  have hq : ‖(t₀,t₀)‖<r := by simpa using ht₀.trans_le (min_le_left _ _)
  have hh := hLip (t,t₀) (t₀,t₀) hp hq
  simpa [div_self hn,Prod.norm_def] using hh

/-- Finite product error, requiring only the proved scalar factor errors. -/
theorem finite_product_relative_error {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    ‖(∏ i∈s, f i)-1‖≤Real.exp (∑ i∈s, ‖f i-1‖)-1 := by
  simpa only [add_sub_cancel] using s.norm_prod_one_add_sub_one_le (fun i => f i-1)

theorem finite_product_relative_error_small {ι : Type*} (s : Finset ι) (f : ι → ℂ)
    {a : ℝ} (ha : 0≤a) (hsum : (∑ i∈s, ‖f i-1‖)≤a) (ha1 : a≤1) :
    ‖(∏ i∈s, f i)-1‖≤2*a := by
  have h := Complex.norm_exp_sub_one_le (x := (a:ℂ)) (by simpa [abs_of_nonneg ha] using ha1)
  have hexp : Real.exp a-1≤2*a := by
    simpa only [←Complex.ofReal_exp,←Complex.ofReal_one,←Complex.ofReal_sub,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr (Real.one_le_exp ha)),
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ha] using h
  exact (finite_product_relative_error s f).trans
    ((sub_le_sub_right (Real.exp_le_exp.mpr hsum) 1).trans hexp)

end
end IsingBulk.Anisotropic.NegativeNormalForm
