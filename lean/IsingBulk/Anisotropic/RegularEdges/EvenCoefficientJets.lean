import IsingBulk.Anisotropic.RegularEdges.EvenModelPhase
import IsingBulk.Anisotropic.RegularEdges.ScaledPositiveJets

namespace IsingBulk.Anisotropic.RegularEdges
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.HT.Contour IsingBulk.Anisotropic.NegativeDominance
open Set Filter MeasureTheory
open scoped Topology BigOperators

def shiftedDependentAngles (n : ℕ) (q : Fin n→ℝ) : Fin (n+1)→ℝ :=
  physicalDependentAngles n (fun i => q i+Real.pi)

theorem shiftedDependentAngles_continuous (n : ℕ) : Continuous (shiftedDependentAngles n) :=
  (physicalDependentAngles_continuous n).comp (by fun_prop)

theorem unscaledAngularCoefficient_pi_shift_eq (n : ℕ) {lam : ℝ} {z : ℂ}
    (hz : z∉spectralSet lam) (hs : spectralS z≠0) :
    unscaledAngularCoefficient n lam z=edgeCoefficientNormalization n*
      ∫q in Icc (fun _ => -Real.pi) (fun _ => Real.pi),
        complexAngularDensity lam z (fun i => (shiftedDependentAngles n q i:ℂ)) := by
  unfold unscaledAngularCoefficient
  rw [multiAngleIntegral_eq_box n _ (complexAngularDensity_dependent_continuous n hz hs),
    angleBox_integral_eq_centered_pi_shift]
  rfl

theorem shiftedWeightedCoefficient_iteratedDeriv (n j : ℕ)
    {lam : ℝ} {zeta W : ℂ→ℂ} {U : Set ℂ} (hU : IsOpen U)
    (ha : AnalyticOnNhd ℂ zeta U) (hW : AnalyticOnNhd ℂ W U)
    (hz : ∀u∈U,zeta u∉spectralSet lam) (hs : ∀u∈U,spectralS (zeta u)≠0) {u : ℂ} (hu : u∈U) :
    iteratedDeriv j (fun v => W v*unscaledAngularCoefficient n lam (zeta v)) u=
      edgeCoefficientNormalization n*∫q in Icc (fun _ => -Real.pi) (fun _ => Real.pi),
        iteratedDeriv j (fun v => W v*complexAngularDensity lam (zeta v)
          (fun i => (shiftedDependentAngles n q i:ℂ))) u := by
  let K : Set (Fin n→ℝ) := Icc (fun _ => -Real.pi) (fun _ => Real.pi)
  have heq : (fun v => W v*unscaledAngularCoefficient n lam (zeta v))=ᶠ[𝓝 u]
      (fun v => ∫q in K,edgeCoefficientNormalization n*(W v*complexAngularDensity lam (zeta v)
        (fun i => (shiftedDependentAngles n q i:ℂ)))) := by
    filter_upwards [hU.mem_nhds hu] with v hv
    rw [unscaledAngularCoefficient_pi_shift_eq n (hz v hv) (hs v hv),integral_const_mul,integral_const_mul]
    ring
  rw [heq.iteratedDeriv_eq j,
    weightedAngularDensity_integral_iteratedDeriv (K:=K) (mu:=volume) isCompact_Icc (by omega : 0<n+1)
      (shiftedDependentAngles n) (shiftedDependentAngles_continuous n) hU ha hW hz hs
      (edgeCoefficientNormalization n) j hu,integral_const_mul]

theorem unscaledAngularCoefficient_negative_fullJet_eq (n j : ℕ) (hn : Even (n+1))
    {lam b : ℝ} {zeta B S : ℂ→ℂ} {U : Set ℂ} (hU : IsOpen U)
    (ha : AnalyticOnNhd ℂ zeta U) (hz : ∀u∈U,zeta u∉spectralSet lam)
    (hs : ∀u∈U,spectralS (zeta u)≠0)
    (hB : ∀u∈U,B u= -spectralT lam (zeta u)/spectralS (zeta u))
    (hS : ∀u∈U,S u=spectralS (zeta u))
    (he : ∀u∈U,edgeMapV lam (-1) (zeta u)=(b:ℂ)+u)
    (hup : ∀u∈U,0<u.im) (hBi : ∀u∈U,0<(B u).im) {u : ℂ} (hu : u∈U) :
    iteratedDeriv j (fun v => unscaledAngularCoefficient n lam (zeta v)) u=
      edgeCoefficientNormalization n*edgeFullDerivativeIntegral (n := n) b B (fun v => Complex.I*S v) j u := by
  have hj := shiftedWeightedCoefficient_iteratedDeriv n j hU ha
    (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : ℂ => (1:ℂ)) U) hz hs hu
  simp only [one_mul] at hj
  rw [hj]
  unfold edgeFullDerivativeIntegral edgeCenteredCube
  congr 1
  apply integral_congr_ae
  apply Eventually.of_forall
  intro q
  apply EventuallyEq.iteratedDeriv_eq
  filter_upwards [hU.mem_nhds hu] with v hv
  exact complexAngularDensity_negative_even_model hn (hB v hv) (hS v hv) (he v hv) (hup v hv) (hBi v hv) q

end
end IsingBulk.Anisotropic.RegularEdges
