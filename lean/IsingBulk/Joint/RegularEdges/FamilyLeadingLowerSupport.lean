import IsingBulk.Anisotropic.RegularEdges.EvenScaledJets
import IsingBulk.Joint.RegularEdges.FamilyLeadingLocal
import IsingBulk.Joint.RegularEdges.FamilyFiniteCoefficients

namespace IsingBulk.Joint.RegularEdges
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.Anisotropic.RegularEdges MeasureTheory Set Filter Metric
open scoped Topology BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem shapeDenominator_norm_le_two_upper {n : ℕ} {b : ℝ} {B : ℂ→ℂ}
    {t : ℝ} (ht : 0<t) (hB : 0<(B (Complex.I*(t:ℂ)^2)).im) (x : ShapeSpace n) :
    ‖edgeShapeDenominator b B t x‖≤2 := by
  have hu : 0<(Complex.I*(t:ℂ)^2).im := by
    simp only [←Complex.ofReal_pow,Complex.mul_im,Complex.I_re,Complex.I_im,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,one_mul,zero_add]
    positivity
  have hp : ‖∏ i,edgeParamRoot b B (Complex.I*(t:ℂ)^2) (x.1 i)‖≤1 := by
    rw [norm_prod]
    exact Finset.prod_le_one₀ (fun _ _=>norm_nonneg _) (fun i _=>(edgeParamRoot_norm_lt_one_upper b hu hB.le (x.1 i)).le)
  change ‖1-∏ i,edgeComplexRoot b B (Complex.I*(t:ℂ)^2) (x.1 i:ℂ)‖≤2
  simp_rw [edgeComplexRoot_real]
  calc
    _ ≤ ‖(1:ℂ)‖+‖∏ i,edgeParamRoot b B (Complex.I*(t:ℂ)^2) (x.1 i)‖ := norm_sub_le _ _
    _ ≤ 2 := by rw [norm_one]; linarith

omit [NormedSpace ℂ E] in
theorem family_shapeDenominator_filtered_zero {α : Type*} {l : Filter α}
    {τ : α → ℝ} (hτ : Tendsto τ l (𝓝[>] 0)) {eta : α → E} {eta₀ : E}
    (heta : Tendsto eta l (𝓝 eta₀)) {n : ℕ} {b : ℝ} {B : ℂ × E → ℂ}
    (hb : |b|<1) (hB : ContinuousAt B (0,eta₀))
    (hres : continuedRoot (b:ℂ)^(n+1)=1) (x : ShapeSpace n) :
    Tendsto (fun t : α => edgeShapeDenominator b (fun u=>B (u,eta t))
      (τ t) (τ t • x)) l (𝓝 0) := by
  have hz : Tendsto (fun t : α => (τ t:ℂ)) l (𝓝 0) := by
    simpa using! Complex.continuous_ofReal.continuousAt.tendsto.comp
      (hτ.mono_right nhdsWithin_le_nhds)
  have hh := (family_shapeDenominator_filtered_limit hτ heta hb hB hres x).mul (hz.pow 2)
  simp only [zero_pow (by omega : 2≠0),mul_zero] at hh
  apply hh.congr'
  filter_upwards [hτ.eventually self_mem_nhdsWithin] with t ht
  exact div_mul_cancel₀ _ (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (show (0:ℝ)<τ t from ht).ne'))

end
end IsingBulk.Joint.RegularEdges
