import IsingBulk.Anisotropic.NegativeNormalForm.JointPhaseAnalytic

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open scoped Topology

theorem phaseFirstFactor_identity (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) (d t v : ℂ)
    (hc0 : Complex.cosh (negativePhase B phi hphi t d)=negativeDispersion B (Real.cos phi) t d)
    (hc1 : Complex.cosh (negativePhase B phi hphi t (d+v))=negativeDispersion B (Real.cos phi) t (d+v))
    (hS : hyperbolicDivisor (negativePhase B phi hphi t d) (phaseIncrement B phi hphi d t v) ≠ 0) :
    phaseIncrement B phi hphi d t v=v*phaseFirstFactor B phi hphi d t v := by
  have hf := cosh_increment_factor (negativePhase B phi hphi t d) (phaseIncrement B phi hphi d t v)
  have he : negativePhase B phi hphi t d+phaseIncrement B phi hphi d t v =
      negativePhase B phi hphi t (d+v) := by unfold phaseIncrement; ring
  rw [he, hc0, hc1] at hf
  have hk := cosineFirstFactor_identity B d t v
  have heq : phaseIncrement B phi hphi d t v *
      hyperbolicDivisor (negativePhase B phi hphi t d) (phaseIncrement B phi hphi d t v) =
        v*cosineFirstFactor B d t v := by
    rw [← hf, ← hk]
    unfold negativeDispersion
    ring
  unfold phaseFirstFactor
  rw [← mul_div_assoc, eq_div_iff hS]
  exact heq

theorem phaseSecondFactor_identity (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) (d t v : ℂ)
    (hfirst : phaseIncrement B phi hphi d t v=v*phaseFirstFactor B phi hphi d t v)
    (hS : hyperbolicDivisor (negativePhase B phi hphi t d) (phaseIncrement B phi hphi d t v) ≠ 0)
    (hS0 : Complex.sinh (negativePhase B phi hphi t d) ≠ 0) :
    phaseFirstFactor B phi hphi d t v-phaseFirstFactor B phi hphi d t 0 =
      v*phaseSecondFactor B phi hphi d t v := by
  have hden := hyperbolicDivisor_increment (negativePhase B phi hphi t d)
    (phaseIncrement B phi hphi d t v)
  nth_rw 2 [hfirst] at hden
  have hk := cosineSecondFactor_identity B d t v
  change cosineFirstFactor B d t v /
      hyperbolicDivisor (negativePhase B phi hphi t d) (phaseIncrement B phi hphi d t v) -
    phaseFirstFactor B phi hphi d t 0 = _
  have hzero : phaseFirstFactor B phi hphi d t 0 =
      cosineFirstFactor B d t 0/Complex.sinh (negativePhase B phi hphi t d) := by
    simp [phaseFirstFactor, phaseIncrement]
  rw [hzero]
  unfold phaseSecondFactor
  field_simp
  linear_combination 2*(Complex.sinh (negativePhase B phi hphi t d))*hk -
    2*(cosineFirstFactor B d t 0)*hden


theorem negativePhase_cosh_eventually (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) (d : ℂ) (hB : AnalyticAt ℂ B (1-Complex.cos d)) :
    ∀ᶠ z : ℂ × ℂ in 𝓝 (1-Complex.cos d,d),
      Complex.cosh (negativePhase B phi hphi z.1 z.2)=negativeDispersion B (Real.cos phi) z.1 z.2 := by
  have hW : AnalyticAt ℂ (fun z : ℂ × ℂ => negativeDispersion B (Real.cos phi) z.1 z.2)
      (1-Complex.cos d,d) := by
    exact analyticAt_const.add ((hB.comp (f := fun z : ℂ × ℂ => z.1) analyticAt_fst).mul
      ((analyticAt_fst.sub analyticAt_const).add (Complex.analyticAt_cos.comp
        (f := fun z : ℂ × ℂ => z.2) analyticAt_snd)))
  have he := (edgePhase_spec phi hphi).2.2.1
  rw [← negativeDispersion_center B (Real.cos phi) d] at he
  exact hW.continuousAt.tendsto.eventually he

/-- Both divisions hold simultaneously on an actual open neighborhood in (t,v). -/
theorem phase_factors_eventually (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) (d : ℂ) (hB : AnalyticAt ℂ B (1-Complex.cos d)) :
    ∀ᶠ z : ℂ × ℂ in 𝓝 (1-Complex.cos d,0),
      phaseIncrement B phi hphi d z.1 z.2=z.2*phaseFirstFactor B phi hphi d z.1 z.2 ∧
      phaseFirstFactor B phi hphi d z.1 z.2-phaseFirstFactor B phi hphi d z.1 0 =
        z.2*phaseSecondFactor B phi hphi d z.1 z.2 := by
  have hc := negativePhase_cosh_eventually B phi hphi d hB
  have ht0 : ContinuousAt (fun z : ℂ × ℂ => (z.1,d)) (1-Complex.cos d,0) :=
    continuousAt_fst.prodMk continuousAt_const
  have ht1 : ContinuousAt (fun z : ℂ × ℂ => (z.1,d+z.2)) (1-Complex.cos d,0) :=
    continuousAt_fst.prodMk (continuousAt_const.add continuousAt_snd)
  have hc0 := ht0.tendsto.eventually hc
  have hc1 := ht1.tendsto.eventually (by simpa only [add_zero] using hc)
  obtain ⟨h0,hi⟩ := phase_base_and_increment_analyticAt B phi hphi d hB
  have hden := (hyperbolicDivisor_analyticAt (negativePhase B phi hphi (1-Complex.cos d) d)).comp_of_eq
    (h0.prod hi) (by simp [phaseIncrement])
  have hS : ∀ᶠ z : ℂ × ℂ in 𝓝 (1-Complex.cos d,0),
      hyperbolicDivisor (negativePhase B phi hphi z.1 d) (phaseIncrement B phi hphi d z.1 z.2) ≠ 0 :=
    hden.continuousAt.eventually_ne (by simpa [phaseIncrement] using phase_sinh_center_ne_zero B phi hphi d)
  have hS0 := (Complex.analyticAt_sinh.comp h0).continuousAt.eventually_ne
    (phase_sinh_center_ne_zero B phi hphi d)
  filter_upwards [hc0,hc1,hS,hS0] with z hz0 hz1 hzS hzS0
  have hfirst := phaseFirstFactor_identity B phi hphi d z.1 z.2 hz0 hz1 hzS
  exact ⟨hfirst,phaseSecondFactor_identity B phi hphi d z.1 z.2 hfirst hzS hzS0⟩

end
end IsingBulk.Anisotropic.NegativeNormalForm
