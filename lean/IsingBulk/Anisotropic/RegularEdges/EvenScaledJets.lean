import IsingBulk.Anisotropic.RegularEdges.EvenCoefficientJets

namespace IsingBulk.Anisotropic.RegularEdges
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.HT.Contour IsingBulk.Anisotropic.NegativeDominance
open Set Filter MeasureTheory
open scoped Topology BigOperators

theorem edgeParamRoot_norm_lt_one_upper (b : ℝ) {B : ℂ→ℂ} {u : ℂ}
    (hu : 0<u.im) (hB : 0≤(B u).im) (q : ℝ) : ‖edgeParamRoot b B u q‖<1 := by
  have hw : 0<(edgeParamW b B u q).im := by
    have hm := mul_nonneg hB (sub_nonneg.mpr (Real.cos_le_one q))
    simp only [edgeParamW,Complex.add_im,Complex.ofReal_im,zero_add,Complex.mul_im,
      Complex.sub_re,Complex.one_re,Complex.ofReal_re,Complex.sub_im,Complex.one_im,sub_zero,mul_zero,zero_add]
    linarith
  rw [edgeParamRoot,continuedRoot_eq_interiorRoot hw]
  exact interiorRoot_norm_lt_one hw

theorem edgeAngularDensity_eq_fullIntegrand_upper {N : ℕ} (hN : 0<N)
    (b : ℝ) (B S : ℂ→ℂ) {u : ℂ} (hu : 0<u.im) (hB : 0≤(B u).im) (q : Fin N→ℝ) :
    edgeAngularDensity b B S u q=edgeFullIntegrand b B S u q := by
  have hd := one_sub_coordinateProduct_ne_zero hN (fun i => edgeParamRoot_norm_lt_one_upper b hu hB (q i))
  change 1-∏i,edgeParamRoot b B u (q i)≠0 at hd
  unfold edgeAngularDensity
  rw [edgeAngularWeight_eq_edgeNumerator]
  unfold edgeFullIntegrand edgeRootProduct
  field_simp [hd]
  ring

theorem scaledNegativeEvenCoefficient_iteratedDeriv (n j : ℕ) (hn : Even (n+1))
    {lam b : ℝ} {B S A zeta : ℂ→ℂ} {U : Set ℂ} (hU : IsOpen U)
    (ha : AnalyticOnNhd ℂ zeta U) (hAa : AnalyticOnNhd ℂ A U)
    (hz : ∀u∈U,zeta u∉spectralSet lam) (hs : ∀u∈U,spectralS (zeta u)≠0)
    (hB : ∀u∈U,B u= -spectralT lam (zeta u)/spectralS (zeta u))
    (hS : ∀u∈U,S u=spectralS (zeta u))
    (he : ∀u∈U,edgeMapV lam (-1) (zeta u)=(b:ℂ)+u)
    (hup : ∀u∈U,0<u.im) (hBi : ∀u∈U,0<(B u).im) {u : ℂ} (hu : u∈U) :
    iteratedDeriv j (fun v => (A v)^(n+1)*unscaledAngularCoefficient n lam (zeta v)) u=
      ((n+1).factorial:ℂ)⁻¹*∫q : Fin n→ℝ,
        iteratedDeriv j (fun v => edgeFullIntegrand b B (fun w => Complex.I*S w/A w) v
          (centeredFullAngles n q)) u ∂Measure.pi (fun _ => edgeAngleMeasure) := by
  rw [shiftedWeightedCoefficient_iteratedDeriv n j (W := fun v => A v^(n+1)) hU ha (fun v hv => (hAa v hv).pow (n+1)) hz hs hu]
  have hd (v : ℂ) (hv : v∈U) (q : Fin n→ℝ) :
      (A v)^(n+1)*complexAngularDensity lam (zeta v) (fun i => (shiftedDependentAngles n q i:ℂ))=
        edgeFullIntegrand b B (fun w => Complex.I*S w/A w) v (centeredFullAngles n q) := by
    rw [edgeFullIntegrand_div_scale]
    congr 1
    rw [←edgeAngularDensity_eq_fullIntegrand_upper (by omega) b B (fun w => Complex.I*S w)
      (hup v hv) (hBi v hv).le]
    dsimp only [shiftedDependentAngles]
    rw [complexAngularDensity_negative_even_model hn (hB v hv) (hS v hv) (he v hv) (hup v hv) (hBi v hv)]
    exact (edgeAngularDensity_wrapAngle b B (fun w => Complex.I*S w) v (physicalDependentAngles n q)).symm
  have hdj (q : Fin n→ℝ) :
      iteratedDeriv j (fun v => (A v)^(n+1)*complexAngularDensity lam (zeta v)
        (fun i => (shiftedDependentAngles n q i:ℂ))) u=
      iteratedDeriv j (fun v => edgeFullIntegrand b B (fun w => Complex.I*S w/A w) v
        (centeredFullAngles n q)) u := by
    apply EventuallyEq.iteratedDeriv_eq
    filter_upwards [hU.mem_nhds hu] with v hv using hd v hv q
  simp_rw [hdj]
  rw [edgeAngleMeasure_integral_eq]
  dsimp [edgeCoefficientNormalization]
  ring

end
end IsingBulk.Anisotropic.RegularEdges
