import IsingBulk.Anisotropic.RegularEdges.LeadingFull
import IsingBulk.Anisotropic.RegularEdges.LeadingHigher

namespace IsingBulk.Anisotropic.RegularEdges
noncomputable section
open IsingBulk.First IsingBulk.Tail Set Filter Metric MeasureTheory
open scoped Topology

/-- Finite higher particle orders are bounded after full angular integration, not merely locally. -/
theorem edgeFullDerivativeIntegral_higher_bounded {n j : ℕ} (hn : 1≤n)
    (hdegree : 2*(j+1)≤(n+1)*n) {b : ℝ} {B S : ℂ→ℂ}
    (hb : |b|<1) (hB : AnalyticAt ℂ B 0) (hBi : 0<(B 0).im)
    (hS : AnalyticAt ℂ S 0) (hS0 : S 0≠0) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ t : ℝ in 𝓝[>] 0,
      ‖edgeFullDerivativeIntegral (n := n) b B S j (Complex.I*(t:ℂ)^2)‖≤C := by
  obtain ⟨r,δ,M,hr,hδ,hM,hpoint⟩ := edge_higher_derivative_pointwise_bound hn hdegree hb hB hBi hS hS0
  let R := min r Real.pi
  have hR : 0<R := lt_min hr Real.pi_pos
  have hRπ : R≤Real.pi := min_le_right _ _
  obtain ⟨C,hC,hcomp⟩ := edgeComplementDerivativeIntegral_bounded (n := n) hb hB hBi hS hS0 hR j
  have htend : Tendsto (fun t : ℝ => Complex.I*(t:ℂ)^2) (𝓝[>] 0) (𝓝 0) := by
    simpa using! ((by fun_prop : Continuous (fun t : ℝ => Complex.I*(t:ℂ)^2)).tendsto 0).mono_left nhdsWithin_le_nhds
  refine ⟨M*volume.real (edgeCenteredCube n)+C,by positivity,?_⟩
  filter_upwards [self_mem_nhdsWithin,(eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds,
    htend.eventually hcomp,
    edgeFullDerivativeIntegral_eventually_decomposition (n := n) hb hB hBi hS hS0 hR hRπ j]
    with t ht htδ hcb heq
  have hlocal : ‖∫ q in edgeCenteredCube n,edgeShapeCutoff R (edgeFreeShape q)*
      edgeConstrainedJet b B S j (Complex.I*(t:ℂ)^2,q)‖≤M*volume.real (edgeCenteredCube n) := by
    apply norm_setIntegral_le_of_norm_le_const isCompact_Icc.measure_lt_top
    intro q _
    by_cases hz : edgeShapeCutoff R (edgeFreeShape q)=0
    · simpa only [hz,zero_mul,norm_zero] using hM
    · have hx := (edgeShapeCutoff_properties (n := n) hR).2.2.2 _ hz
      have hp := hpoint t ht htδ (edgeFreeShape q) (hx.trans_le (min_le_left _ _))
      rw [norm_mul]
      calc
        _ ≤ 1*M := mul_le_mul ((edgeShapeCutoff_properties (n := n) hR).2.2.1 _)
          hp (norm_nonneg _) zero_le_one
        _ = M := one_mul _
  rw [heq,←edge_local_derivative_integral_eq b B S hR hRπ t]
  exact (norm_add_le _ _).trans (add_le_add hlocal hcb)

/-- Every lower nonresonant particle order has bounded jets on the complete centered cube. -/
theorem edgeFullDerivativeIntegral_nonresonant_bounded {n : ℕ} {b : ℝ} {B S : ℂ→ℂ}
    (hb : |b|<1) (hB : AnalyticAt ℂ B 0) (hBi : 0<(B 0).im)
    (hS : AnalyticAt ℂ S 0) (hS0 : S 0≠0) (hres : continuedRoot (b:ℂ)^(n+1)≠1) (j : ℕ) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ u in 𝓝 (0:ℂ),‖edgeFullDerivativeIntegral (n := n) b B S j u‖≤C := by
  obtain ⟨C,hC,hev⟩ := edgeConstrainedJet_nonresonant_bound hb hB hBi hS hS0 hres j
  refine ⟨C*volume.real (edgeCenteredCube n),by positivity,?_⟩
  filter_upwards [hev] with u hu
  apply norm_setIntegral_le_of_norm_le_const isCompact_Icc.measure_lt_top
  intro q hq
  exact (hu q (fun i => ⟨hq.1 i,hq.2 i⟩)).2

end
end IsingBulk.Anisotropic.RegularEdges
