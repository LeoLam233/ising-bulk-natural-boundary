import IsingBulk.Anisotropic.RegularEdges.LeadingAnalytic

namespace IsingBulk.Anisotropic.RegularEdges
noncomputable section
open IsingBulk.First IsingBulk.Tail Set Filter
open scoped Topology BigOperators

def edgeAnalyticJet {N : ℕ} (b : ℝ) (B S : ℂ→ℂ) (j : ℕ) (p : ℂ×(Fin N→ℂ)) : ℂ :=
  quotientJetNumerator (fun u => edgeComplexAmplitude b B S (u,p.2))
    (fun u => edgeComplexDenominator b B (u,p.2)) j p.1

theorem edgeAnalyticJet_analyticAt {N : ℕ} {b : ℝ} {B S : ℂ→ℂ}
    (hb : |b|<1) (hB : AnalyticAt ℂ B 0) (hBi : 0<(B 0).im)
    (hS : AnalyticAt ℂ S 0) (hS0 : S 0≠0) (j : ℕ) :
    AnalyticAt ℂ (@edgeAnalyticJet N b B S j) (0,0) :=
  quotientJetNumerator_joint_analyticAt (edgeComplexAmplitude_analyticAt hb hB hBi hS hS0)
    (edgeComplexDenominator_analyticAt hb hB) j

theorem edgeComplexDenominator_parameter_hasDerivAt {N : ℕ} (hN : 0<N) {b : ℝ}
    (hb : |b|<1) (B : ℂ→ℂ) (hres : continuedRoot (b:ℂ)^N=1) :
    HasDerivAt (fun u => edgeComplexDenominator b B (u,(0:Fin N→ℂ)))
      (-(N:ℂ)*Complex.I/(Real.sqrt (1-b^2):ℂ)) 0 := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  have h := ((edgeParamRoot_parameter_hasDerivAt hb B).pow (n+1)).const_sub 1
  have hc : -((n+1:ℂ)*continuedRoot (b:ℂ)^n*
      (Complex.I*continuedRoot (b:ℂ)/(Real.sqrt (1-b^2):ℂ)))=
      -(n+1:ℂ)*Complex.I/(Real.sqrt (1-b^2):ℂ) := by
    calc
      _ = (-(n+1:ℂ)*Complex.I/(Real.sqrt (1-b^2):ℂ))*continuedRoot (b:ℂ)^(n+1) := by rw [pow_succ]; ring
      _ = _ := by rw [hres,mul_one]
  simpa [edgeComplexDenominator,edgeComplexRoot,edgeParamRoot,edgeParamW,hc] using h

theorem edgeAnalyticJet_collision {N : ℕ} (hN : 0<N) {b : ℝ} (hb : |b|<1)
    (B S : ℂ→ℂ) (hres : continuedRoot (b:ℂ)^N=1) (j : ℕ) :
    edgeAnalyticJet b B S j (0,(0:Fin N→ℂ))=
      (-1:ℂ)^j*(j.factorial:ℂ)*(-(N:ℂ)*Complex.I/(Real.sqrt (1-b^2):ℂ))^j*
        (2*edgeRegularAmplitude b B S 0 (0:Fin N→ℝ)) := by
  unfold edgeAnalyticJet
  rw [quotientJetNumerator_at_zero (by simp [edgeComplexDenominator,hres]),
    (edgeComplexDenominator_parameter_hasDerivAt hN hb B hres).deriv,
    edgeComplexAmplitude_collision b B S hres]

theorem edgeAnalyticJet_collision_ne_zero {N : ℕ} (hN : 0<N) {b : ℝ}
    (hb : |b|<1) {B S : ℂ→ℂ} (hBi : 0<(B 0).im) (hS0 : S 0≠0)
    (hres : continuedRoot (b:ℂ)^N=1) (j : ℕ) :
    edgeAnalyticJet b B S j (0,(0:Fin N→ℂ))≠0 := by
  have hb' := abs_lt.mp hb
  have hs : (Real.sqrt (1-b^2):ℂ)≠0 := Complex.ofReal_ne_zero.mpr
    (Real.sqrt_pos.mpr (by nlinarith)).ne'
  have hn : (N:ℂ)≠0 := Nat.cast_ne_zero.mpr hN.ne'
  rw [edgeAnalyticJet_collision hN hb B S hres j]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num))
    (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)))
    (pow_ne_zero _ (div_ne_zero (mul_ne_zero (neg_ne_zero.mpr hn) Complex.I_ne_zero) hs)))
    (mul_ne_zero (by norm_num) (edgeRegularAmplitude_collision_ne_zero hb hBi hS0))

theorem edgeAngularDensity_iteratedDeriv {N : ℕ} (b : ℝ) (B S : ℂ→ℂ)
    (q : Fin N→ℝ) (u : ℂ) (j : ℕ)
    (hA : AnalyticAt ℂ (fun v => edgeComplexAmplitude b B S (v,fun i => (q i:ℂ))) u)
    (hD : AnalyticAt ℂ (fun v => edgeComplexDenominator b B (v,fun i => (q i:ℂ))) u)
    (hne : edgeComplexDenominator b B (u,fun i => (q i:ℂ))≠0) :
    iteratedDeriv j (fun v => edgeAngularDensity b B S v q) u=
      (firstVandermonde q:ℂ)^2*edgeSincFactor q*edgeAnalyticJet b B S j (u,fun i => (q i:ℂ))/
        edgeComplexDenominator b B (u,fun i => (q i:ℂ))^(j+1) := by
  simp_rw [edgeAngularDensity_analytic_factorization]
  rw [iteratedDeriv_const_mul_field,iteratedDeriv_quotient_eq hA hD hne]
  simp only [edgeAnalyticJet,mul_div_assoc]

end
end IsingBulk.Anisotropic.RegularEdges
