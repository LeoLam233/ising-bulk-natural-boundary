import IsingBulk.Anisotropic.RegularEdges.LeadingJets
import IsingBulk.Anisotropic.RegularEdges.ShapePeriod

namespace IsingBulk.Anisotropic.RegularEdges
noncomputable section
open IsingBulk.First IsingBulk.Tail Set Filter
open scoped Topology BigOperators

def edgeQuadratic {N : ℕ} (b : ℝ) (B : ℂ) (q : Fin N→ℝ) : ℂ :=
  (N:ℂ)/(Real.sqrt (1-b^2):ℂ)-Complex.I*B/(2*(Real.sqrt (1-b^2):ℂ))*∑ i,(q i:ℂ)^2

theorem edgeQuadratic_re_pos {N : ℕ} (hN : 0<N) {b : ℝ} (hb : |b|<1)
    {B : ℂ} (hB : 0<B.im) (q : Fin N→ℝ) : 0<(edgeQuadratic b B q).re := by
  have hb' := abs_lt.mp hb
  have hs : 0<Real.sqrt (1-b^2) := Real.sqrt_pos.mpr (by nlinarith)
  have hc := edge_quadratic_re_pos hB (mul_pos (by norm_num : (0:ℝ)<2) hs)
  have he : edgeQuadratic b B q=
      (((N:ℝ)/Real.sqrt (1-b^2):ℝ):ℂ)+
      (-Complex.I*B/((2*Real.sqrt (1-b^2):ℝ):ℂ))*((∑ i,(q i)^2:ℝ):ℂ) := by
    unfold edgeQuadratic
    push_cast
    ring
  rw [he]
  have hp : 0<(N:ℝ)/Real.sqrt (1-b^2) := div_pos (by exact_mod_cast hN) hs
  have hq : 0≤∑ i,(q i)^2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  simpa only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,mul_zero,sub_zero] using
    add_pos_of_pos_of_nonneg hp (mul_nonneg hc.le hq)

theorem edgeSincFactor_continuous (N : ℕ) : Continuous (@edgeSincFactor N) := by
  unfold edgeSincFactor
  apply continuous_finsetProd
  intro p _
  exact (Complex.continuous_ofReal.comp (Real.continuous_sinc.comp (by fun_prop))).pow 2

@[simp] theorem edgeSincFactor_zero (N : ℕ) : edgeSincFactor (0:Fin N→ℝ)=1 := by
  simp [edgeSincFactor]

theorem edgeAnalyticJet_scaled_limit {N : ℕ} {b : ℝ} {B S : ℂ→ℂ}
    (hb : |b|<1) (hB : AnalyticAt ℂ B 0) (hBi : 0<(B 0).im)
    (hS : AnalyticAt ℂ S 0) (hS0 : S 0≠0) (j : ℕ) (q : Fin N→ℝ) :
    Tendsto (fun t : ℝ => edgeAnalyticJet b B S j (Complex.I*(t:ℂ)^2,fun i => (t*q i:ℝ)))
      (𝓝[>] 0) (𝓝 (edgeAnalyticJet b B S j (0,(0:Fin N→ℂ)))) := by
  have hp : Continuous (fun t : ℝ => (Complex.I*(t:ℂ)^2,fun i : Fin N => ((t*q i:ℝ):ℂ))) := by fun_prop
  have ht : Tendsto (fun t : ℝ => (Complex.I*(t:ℂ)^2,fun i : Fin N => ((t*q i:ℝ):ℂ)))
      (𝓝[>] 0) (𝓝 ((0,0):ℂ×(Fin N→ℂ))) := by
    simpa using! (hp.tendsto 0).mono_left nhdsWithin_le_nhds
  exact (edgeAnalyticJet_analyticAt hb hB hBi hS hS0 j).continuousAt.tendsto.comp ht

/-- Pointwise blow-up limit of the exact derivative numerator and actual lattice denominator. -/
theorem edge_rescaled_jet_limit {N : ℕ} (hN : 0<N) {b : ℝ} {B S : ℂ→ℂ}
    (hb : |b|<1) (hB : AnalyticAt ℂ B 0) (hBi : 0<(B 0).im)
    (hS : AnalyticAt ℂ S 0) (hS0 : S 0≠0) (hres : continuedRoot (b:ℂ)^N=1)
    (j : ℕ) (q : Fin N→ℝ) :
    Tendsto (fun t : ℝ => (firstVandermonde q:ℂ)^2*edgeSincFactor (fun i => t*q i)*
      edgeAnalyticJet b B S j (Complex.I*(t:ℂ)^2,fun i => ((t*q i:ℝ):ℂ))/
      (edgeComplexDenominator b B (Complex.I*(t:ℂ)^2,fun i => ((t*q i:ℝ):ℂ))/(t:ℂ)^2)^(j+1))
      (𝓝[>] 0) (𝓝 ((firstVandermonde q:ℂ)^2*edgeAnalyticJet b B S j (0,(0:Fin N→ℂ))/
        edgeQuadratic b (B 0) q^(j+1))) := by
  have hs : Tendsto (fun t : ℝ => edgeSincFactor (fun i => t*q i)) (𝓝[>] 0) (𝓝 (1:ℂ)) := by
    have hc : Continuous (fun t : ℝ => edgeSincFactor (fun i => t*q i)) :=
      (edgeSincFactor_continuous N).comp (by fun_prop)
    simpa [edgeSincFactor] using! (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hd : Tendsto (fun t : ℝ => edgeComplexDenominator b B
      (Complex.I*(t:ℂ)^2,fun i => ((t*q i:ℝ):ℂ))/(t:ℂ)^2) (𝓝[>] 0)
      (𝓝 (edgeQuadratic b (B 0) q)) := by
    simpa only [edgeComplexDenominator,edgeRootProduct,edgeQuadratic,edgeComplexRoot_real] using
      edgeRootProduct_scaled_denominator_limit hb hB.continuousAt q hres
  have hn : edgeQuadratic b (B 0) q≠0 := by
    intro he
    have hh := edgeQuadratic_re_pos hN hb hBi q
    simp [he] at hh
  simpa only [mul_one,Pi.div_apply] using! ((hs.const_mul ((firstVandermonde q:ℂ)^2)).mul
    (edgeAnalyticJet_scaled_limit hb hB hBi hS hS0 j q)).div (hd.pow (j+1)) (pow_ne_zero _ hn)

end
end IsingBulk.Anisotropic.RegularEdges
