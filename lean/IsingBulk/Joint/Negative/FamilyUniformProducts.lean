import IsingBulk.Joint.Negative.FamilySeriesLimit
import Mathlib.Topology.Algebra.IsUniformGroup.Basic

namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter Metric
open scoped Topology BigOperators

/-- Uniform convergence of actual complex products, with the necessary common
bound on one moving factor and the other boundary factor stated explicitly. -/
theorem uniform_product_of_common_bounds {I E : Type*} {l : Filter I}
    {f g : I→E→ℂ} {f₀ g₀ : E→ℂ} {Q : Set E}
    (hf : TendstoUniformlyOn f f₀ l Q) (hg : TendstoUniformlyOn g g₀ l Q)
    {A B : ℝ} (hA : 0≤A) (hB : 0≤B)
    (hfb : ∀ᶠt in l,∀eta∈Q,‖f t eta‖≤A) (hgb : ∀eta∈Q,‖g₀ eta‖≤B) :
    TendstoUniformlyOn (fun t eta=>f t eta*g t eta) (fun eta=>f₀ eta*g₀ eta) l Q := by
  rw [Metric.tendstoUniformlyOn_iff] at hf hg ⊢
  intro ε hε
  let d := ε/(A+B+1)
  have hden : 0<A+B+1 := by positivity
  have hd : 0<d := div_pos hε hden
  filter_upwards [hf d hd,hg d hd,hfb] with t hft hgt hbt eta heta
  have hfe : ‖f t eta-f₀ eta‖<d := by simpa only [dist_eq_norm,norm_sub_rev] using hft eta heta
  have hge : ‖g t eta-g₀ eta‖<d := by simpa only [dist_eq_norm,norm_sub_rev] using hgt eta heta
  have he : f t eta*g t eta-f₀ eta*g₀ eta=
      f t eta*(g t eta-g₀ eta)+(f t eta-f₀ eta)*g₀ eta := by ring
  rw [dist_eq_norm,norm_sub_rev,he]
  calc
    _ ≤ ‖f t eta*(g t eta-g₀ eta)‖+‖(f t eta-f₀ eta)*g₀ eta‖ := norm_add_le _ _
    _ ≤ A*d+d*B := by
      rw [norm_mul,norm_mul]
      exact add_le_add (mul_le_mul (hbt eta heta) hge.le (norm_nonneg _) hA)
        (mul_le_mul hfe.le (hgb eta heta) (norm_nonneg _) hd.le)
    _ < ε := by have hh : d*(A+B+1)=ε := div_mul_cancel₀ ε hden.ne'; nlinarith

theorem uniform_const_mul {I E : Type*} {l : Filter I} {f : I→E→ℂ} {f₀ : E→ℂ} {Q : Set E}
    (hf : TendstoUniformlyOn f f₀ l Q) (c : ℂ) :
    TendstoUniformlyOn (fun t eta=>c*f t eta) (fun eta=>c*f₀ eta) l Q := by
  let L : ℂ→L[ℂ]ℂ := c • ContinuousLinearMap.id ℂ ℂ
  exact L.uniformContinuous.comp_tendstoUniformlyOn hf

theorem uniform_finset_sum {I E J : Type*} {l : Filter I}
    (F : Finset J) (f : J→I→E→ℂ) (f₀ : J→E→ℂ) {Q : Set E}
    (hf : ∀j∈F,TendstoUniformlyOn (f j) (f₀ j) l Q) :
    TendstoUniformlyOn (fun t eta=>∑j∈F,f j t eta) (fun eta=>∑j∈F,f₀ j eta) l Q := by
  classical
  induction F using Finset.induction_on with
  | empty => simpa using (tendsto_const_nhds : Tendsto (fun _ : I => (0:ℂ)) l (𝓝 0)).tendstoUniformlyOn_const Q
  | @insert a F ha ih =>
    simpa only [Finset.sum_insert ha,Pi.add_def] using
      (hf a (Finset.mem_insert_self _ _)).add (ih (fun j hj=>hf j (Finset.mem_insert_of_mem hj)))

end
end IsingBulk.Joint.Negative
