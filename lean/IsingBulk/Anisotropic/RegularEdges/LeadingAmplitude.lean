import IsingBulk.Anisotropic.RegularEdges.LeadingDerivative
import IsingBulk.Anisotropic.RegularEdges.OddRadialPeriod

namespace IsingBulk.Anisotropic.RegularEdges
noncomputable section
open IsingBulk.First IsingBulk.Tail MeasureTheory Set Filter
open scoped Topology

def edgeLeadingCoefficient (n k : ℕ) (b : ℝ) (B S : ℂ→ℂ) : ℂ :=
  edgeAnalyticJet b B S k (0,(0:Fin (n+1)→ℂ))*
    shapePeriodIntrinsic n k ((n+1)/Real.sqrt (1-b^2))
      (-Complex.I*B 0/((2*Real.sqrt (1-b^2):ℝ):ℂ))

theorem edgeLeadingCoefficient_ne_zero {n k : ℕ} {b : ℝ} {B S : ℂ→ℂ}
    (hb : |b|<1) (hBi : 0<(B 0).im) (hS0 : S 0≠0)
    (hres : continuedRoot (b:ℂ)^(n+1)=1)
    (hperiod : shapePeriod n k ((n+1)/Real.sqrt (1-b^2))
      (-Complex.I*B 0/((2*Real.sqrt (1-b^2):ℝ):ℂ))≠0) :
    edgeLeadingCoefficient n k b B S≠0 := by
  apply mul_ne_zero (edgeAnalyticJet_collision_ne_zero (Nat.succ_pos _) hb hBi hS0 hres k)
  intro he
  apply hperiod
  rw [shapePeriod_eq_intrinsic,he,smul_zero]

/-- Actual angular derivatives, not a model coefficient or an assumed leading limit. -/
theorem exists_edgeActualLocalDerivativeIntegral_limit {n k a : ℕ}
    (hbalance : n+a+(n+1)*n=2*(k+1)) (hmajorant : Integrable (@shapeMajorant n k))
    {b : ℝ} {B S : ℂ→ℂ} (hb : |b|<1) (hB : AnalyticAt ℂ B 0)
    (hBi : 0<(B 0).im) (hS : AnalyticAt ℂ S 0) (hS0 : S 0≠0)
    (hres : continuedRoot (b:ℂ)^(n+1)=1) :
    ∃ R : ℝ,0<R ∧ R≤Real.pi ∧
      Tendsto (fun t : ℝ => (t^a) • edgeActualLocalDerivativeIntegral (n := n) b B S k R t)
        (𝓝[>] 0) (𝓝 (edgeLeadingCoefficient n k b B S)) := by
  obtain ⟨R,hR,hRπ,hlim⟩ := exists_edgeLocalJetIntegral_limit hbalance hmajorant hb hB hBi hS hS0 hres
  obtain ⟨r,hr,heq⟩ := edgeActualLocalDerivativeIntegral_eventually_eq (n := n) hb hB hBi hS hS0
  have hrR : 0<min R r := lt_min hR hr
  refine ⟨min R r,hrR,(min_le_left _ _).trans hRπ,?_⟩
  apply (hlim (min R r) hrR (min_le_left _ _)).congr'
  filter_upwards [heq (min R r) hrR (min_le_right _ _) k] with t ht
  rw [ht]

theorem exists_even_edge_actual_leading_amplitude {n k : ℕ} (hn : 1≤n)
    (hdegree : n-1+(n+1)*n=2*k) {b : ℝ} {B S : ℂ→ℂ}
    (hb : |b|<1) (hB : AnalyticAt ℂ B 0) (hBi : 0<(B 0).im)
    (hS : AnalyticAt ℂ S 0) (hS0 : S 0≠0) (hres : continuedRoot (b:ℂ)^(n+1)=1) :
    edgeLeadingCoefficient n k b B S≠0 ∧ ∃ R : ℝ,0<R ∧ R≤Real.pi ∧
      Tendsto (fun t : ℝ => t • edgeActualLocalDerivativeIntegral (n := n) b B S k R t)
        (𝓝[>] 0) (𝓝 (edgeLeadingCoefficient n k b B S)) := by
  have hb' := abs_lt.mp hb
  have hs : 0<Real.sqrt (1-b^2) := Real.sqrt_pos.mpr (by nlinarith)
  refine ⟨edgeLeadingCoefficient_ne_zero hb hBi hS0 hres
    (shapePeriod_rightHalfPlane_ne_zero hn hdegree (div_pos (by positivity) hs)
      (edge_quadratic_re_pos hBi (mul_pos (by norm_num : (0:ℝ)<2) hs))),?_⟩
  simpa using exists_edgeActualLocalDerivativeIntegral_limit (a := 1)
    (by omega : n+1+(n+1)*n=2*(k+1)) (shapeMajorant_integrable hn hdegree) hb hB hBi hS hS0 hres

theorem exists_odd_edge_actual_leading_amplitude {n m : ℕ} (hn : 1≤n)
    (hdegree : n-1+(n+1)*n=2*m+1) {b : ℝ} {B S : ℂ→ℂ}
    (hb : |b|<1) (hB : AnalyticAt ℂ B 0) (hBi : 0<(B 0).im)
    (hS : AnalyticAt ℂ S 0) (hS0 : S 0≠0) (hres : continuedRoot (b:ℂ)^(n+1)=1) :
    edgeLeadingCoefficient n (m+1) b B S≠0 ∧ ∃ R : ℝ,0<R ∧ R≤Real.pi ∧
      Tendsto (fun t : ℝ => (t^2) • edgeActualLocalDerivativeIntegral (n := n) b B S (m+1) R t)
        (𝓝[>] 0) (𝓝 (edgeLeadingCoefficient n (m+1) b B S)) := by
  have hb' := abs_lt.mp hb
  have hs : 0<Real.sqrt (1-b^2) := Real.sqrt_pos.mpr (by nlinarith)
  refine ⟨edgeLeadingCoefficient_ne_zero hb hBi hS0 hres
    (shapePeriod_odd_ne_zero hn hdegree (div_pos (by positivity) hs)
      (edge_quadratic_re_pos hBi (mul_pos (by norm_num : (0:ℝ)<2) hs))),?_⟩
  exact exists_edgeActualLocalDerivativeIntegral_limit
    (by omega : n+2+(n+1)*n=2*(m+1+1)) (shapeMajorant_odd_integrable hn hdegree)
    hb hB hBi hS hS0 hres

end
end IsingBulk.Anisotropic.RegularEdges
