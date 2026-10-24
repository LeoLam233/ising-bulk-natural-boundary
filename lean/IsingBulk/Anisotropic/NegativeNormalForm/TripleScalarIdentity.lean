import IsingBulk.Anisotropic.NegativeNormalForm.TripleScalarBounds

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open Filter
open scoped Topology

theorem phase_factors_triple_eventually (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (hB : AnalyticAt ℂ B 0) :
    ∀ᶠ p : ScalarTriple in 𝓝 0,
      phaseIncrement B phi hphi p.2.1 p.1 p.2.2=
        p.2.2*phaseFirstFactor B phi hphi p.2.1 p.1 p.2.2 ∧
      phaseFirstFactor B phi hphi p.2.1 p.1 p.2.2-
        phaseFirstFactor B phi hphi p.2.1 p.1 0=
        p.2.2*phaseSecondFactor B phi hphi p.2.1 p.1 p.2.2 := by
  have hcosh : ∀ᶠ p : ℂ × ℂ in 𝓝 (0,0),
      Complex.cosh (negativePhase B phi hphi p.1 p.2)=negativeDispersion B (Real.cos phi) p.1 p.2 := by
    simpa only [Complex.cos_zero,sub_self] using negativePhase_cosh_eventually B phi hphi 0 (by simpa using hB)
  have hbase : ContinuousAt (fun p : ScalarTriple => (p.1,p.2.1)) 0 := by fun_prop
  have hshift : ContinuousAt (fun p : ScalarTriple => (p.1,p.2.1+p.2.2)) 0 := by fun_prop
  have he0 := hbase.tendsto.eventually hcosh
  have hshift' : Tendsto (fun p : ScalarTriple => (p.1,p.2.1+p.2.2)) (𝓝 0) (𝓝 ((0:ℂ),(0:ℂ))) := by
    simpa using hshift.tendsto
  have he1 := hshift'.eventually hcosh
  obtain ⟨h0,hi⟩ := phase_base_increment_triple_analyticAt B phi hphi hB
  have hden := (hyperbolicDivisor_analyticAt (negativePhase B phi hphi 0 0)).fun_comp_of_eq
    (f := fun p : ScalarTriple => (negativePhase B phi hphi p.1 p.2.1,
      phaseIncrement B phi hphi p.2.1 p.1 p.2.2)) (h0.prod hi) (by simp [phaseIncrement])
  have hs0 : Complex.sinh (negativePhase B phi hphi 0 0)≠0 := by
    simpa using phase_sinh_center_ne_zero B phi hphi 0
  have hde : ∀ᶠ p : ScalarTriple in 𝓝 0,
      hyperbolicDivisor (negativePhase B phi hphi p.1 p.2.1)
        (phaseIncrement B phi hphi p.2.1 p.1 p.2.2)≠0 :=
    hden.continuousAt.eventually_ne (by simpa [phaseIncrement] using hs0)
  have hse := (Complex.continuous_sinh.continuousAt.comp h0.continuousAt).eventually_ne hs0
  filter_upwards [he0,he1,hde,hse] with p hp0 hp1 hd hs
  have hfirst := phaseFirstFactor_identity B phi hphi p.2.1 p.1 p.2.2 hp0 hp1 hd
  exact ⟨hfirst,phaseSecondFactor_identity B phi hphi p.2.1 p.1 p.2.2 hfirst hd hs⟩

end
end IsingBulk.Anisotropic.NegativeNormalForm
