import IsingBulk.Anisotropic.RegularEdges.LeadingIntegrability
import IsingBulk.Anisotropic.RegularEdges.LeadingAmplitude
import IsingBulk.Anisotropic.RegularEdges.LeadingLower

namespace IsingBulk.Anisotropic.RegularEdges
noncomputable section
open IsingBulk.First IsingBulk.Tail Set Filter Metric MeasureTheory
open scoped Topology

def edgeFullLeadingCoefficient (n k : ℕ) (b : ℝ) (B S : ℂ→ℂ) : ℂ :=
  (Real.sqrt (n+1))⁻¹ • edgeLeadingCoefficient n k b B S

theorem edgeComplementDerivativeIntegral_scaled_limit {n a : ℕ} (ha : 0<a)
    {b : ℝ} {B S : ℂ→ℂ} (hb : |b|<1) (hB : AnalyticAt ℂ B 0) (hBi : 0<(B 0).im)
    (hS : AnalyticAt ℂ S 0) (hS0 : S 0≠0) {R : ℝ} (hR : 0<R) (j : ℕ) :
    Tendsto (fun t : ℝ => (t^a) • edgeComplementDerivativeIntegral (n := n) b B S j R (Complex.I*(t:ℂ)^2))
      (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C,hC,hev⟩ := edgeComplementDerivativeIntegral_bounded (n := n) hb hB hBi hS hS0 hR j
  have htend : Tendsto (fun t : ℝ => Complex.I*(t:ℂ)^2) (𝓝[>] 0) (𝓝 0) := by
    simpa using! ((by fun_prop : Continuous (fun t : ℝ => Complex.I*(t:ℂ)^2)).tendsto 0).mono_left nhdsWithin_le_nhds
  apply squeeze_zero_norm' (a := fun t : ℝ => ‖t^a‖*C)
  · filter_upwards [htend.eventually hev] with t ht
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left ht (norm_nonneg _)
  · have hh := (((tendsto_id : Tendsto (fun t : ℝ => t) (𝓝 0) (𝓝 0)).pow a).norm.mul_const C)
    simpa [zero_pow (Nat.ne_of_gt ha)] using hh.mono_left nhdsWithin_le_nhds

/-- The first singular amplitude of the full constrained angular integral, with no
assumed local limit or integrability premise. -/
theorem edgeFullDerivativeIntegral_leading_limit {n k a : ℕ} (ha : 0<a)
    (hbalance : n+a+(n+1)*n=2*(k+1)) (hmajorant : Integrable (@shapeMajorant n k))
    {b : ℝ} {B S : ℂ→ℂ} (hb : |b|<1) (hB : AnalyticAt ℂ B 0)
    (hBi : 0<(B 0).im) (hS : AnalyticAt ℂ S 0) (hS0 : S 0≠0)
    (hres : continuedRoot (b:ℂ)^(n+1)=1) :
    Tendsto (fun t : ℝ => (t^a) • edgeFullDerivativeIntegral (n := n) b B S k (Complex.I*(t:ℂ)^2))
      (𝓝[>] 0) (𝓝 (edgeFullLeadingCoefficient n k b B S)) := by
  obtain ⟨R,hR,hRπ,hlim⟩ := exists_edgeActualLocalDerivativeIntegral_limit hbalance hmajorant hb hB hBi hS hS0 hres
  have hcomp := edgeComplementDerivativeIntegral_scaled_limit (n := n) ha hb hB hBi hS hS0 hR k
  have hh := (hlim.const_smul ((Real.sqrt (n+1))⁻¹)).add hcomp
  simp only [add_zero] at hh
  apply hh.congr'
  filter_upwards [edgeFullDerivativeIntegral_eventually_decomposition (n := n) hb hB hBi hS hS0 hR hRπ k] with t ht
  rw [ht,smul_add,smul_comm]

theorem edgeFullDerivativeIntegral_lower_limit {n k a j : ℕ} (ha : 0<a) (hj : j<k)
    (hbalance : n+a+(n+1)*n=2*(k+1)) (hmajorant : Integrable (@shapeMajorant n k))
    {b : ℝ} {B S : ℂ→ℂ} (hb : |b|<1) (hB : AnalyticAt ℂ B 0)
    (hBi : 0<(B 0).im) (hS : AnalyticAt ℂ S 0) (hS0 : S 0≠0)
    (hres : continuedRoot (b:ℂ)^(n+1)=1) :
    Tendsto (fun t : ℝ => (t^a) • edgeFullDerivativeIntegral (n := n) b B S j (Complex.I*(t:ℂ)^2))
      (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨R,hR,hRπ,hlim⟩ := exists_edgeActualLocal_lower_limit hj hbalance hmajorant hb hB hBi hS hS0 hres
  have hcomp := edgeComplementDerivativeIntegral_scaled_limit (n := n) ha hb hB hBi hS hS0 hR j
  have hh := (hlim.const_smul ((Real.sqrt (n+1))⁻¹)).add hcomp
  simp only [smul_zero,add_zero] at hh
  apply hh.congr'
  filter_upwards [edgeFullDerivativeIntegral_eventually_decomposition (n := n) hb hB hBi hS hS0 hR hRπ j] with t ht
  rw [ht,smul_add,smul_comm]

theorem even_edge_full_leading_amplitude {n k : ℕ} (hn : 1≤n)
    (hdegree : n-1+(n+1)*n=2*k) {b : ℝ} {B S : ℂ→ℂ}
    (hb : |b|<1) (hB : AnalyticAt ℂ B 0) (hBi : 0<(B 0).im)
    (hS : AnalyticAt ℂ S 0) (hS0 : S 0≠0) (hres : continuedRoot (b:ℂ)^(n+1)=1) :
    edgeFullLeadingCoefficient n k b B S≠0 ∧
      Tendsto (fun t : ℝ => t • edgeFullDerivativeIntegral (n := n) b B S k (Complex.I*(t:ℂ)^2))
        (𝓝[>] 0) (𝓝 (edgeFullLeadingCoefficient n k b B S)) := by
  refine ⟨smul_ne_zero (inv_ne_zero (ne_of_gt (by positivity : 0<Real.sqrt (n+1))))
    (exists_even_edge_actual_leading_amplitude hn hdegree hb hB hBi hS hS0 hres).1,?_⟩
  simpa using edgeFullDerivativeIntegral_leading_limit (a := 1) (by omega)
    (by omega : n+1+(n+1)*n=2*(k+1)) (shapeMajorant_integrable hn hdegree) hb hB hBi hS hS0 hres

theorem odd_edge_full_leading_amplitude {n m : ℕ} (hn : 1≤n)
    (hdegree : n-1+(n+1)*n=2*m+1) {b : ℝ} {B S : ℂ→ℂ}
    (hb : |b|<1) (hB : AnalyticAt ℂ B 0) (hBi : 0<(B 0).im)
    (hS : AnalyticAt ℂ S 0) (hS0 : S 0≠0) (hres : continuedRoot (b:ℂ)^(n+1)=1) :
    edgeFullLeadingCoefficient n (m+1) b B S≠0 ∧
      Tendsto (fun t : ℝ => (t^2) • edgeFullDerivativeIntegral (n := n) b B S (m+1) (Complex.I*(t:ℂ)^2))
        (𝓝[>] 0) (𝓝 (edgeFullLeadingCoefficient n (m+1) b B S)) := by
  refine ⟨smul_ne_zero (inv_ne_zero (ne_of_gt (by positivity : 0<Real.sqrt (n+1))))
    (exists_odd_edge_actual_leading_amplitude hn hdegree hb hB hBi hS hS0 hres).1,?_⟩
  exact edgeFullDerivativeIntegral_leading_limit (by omega)
    (by omega : n+2+(n+1)*n=2*(m+1+1)) (shapeMajorant_odd_integrable hn hdegree) hb hB hBi hS hS0 hres

end
end IsingBulk.Anisotropic.RegularEdges
