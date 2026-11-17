import IsingBulk.AnisoF002.C03.RegularCoefficientNormal

/-!
# The exact regular-edge pole locus and nonresonant complete coefficients

On the full real cycle the only possible boundary pole has every angle
equal to zero modulo 2 pi.  In the actual independent-angle box this is
one point.  Every nonresonant complete coefficient is analytic across the
selected edge, with all numerator and site factors retained.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open Set MeasureTheory
open scoped Topology BigOperators

theorem phaseSiteFactor_analyticAt_of_denominator {G : ℂ}
    (hG : 1 - Complex.exp (-G) ≠ 0) : AnalyticAt ℂ phaseSiteFactor G := by
  have he : AnalyticAt ℂ (fun z => Complex.exp (-z)) G := analyticAt_id.neg.cexp
  exact (analyticAt_const.add he).div (analyticAt_const.sub he) hG

theorem boundary_pole_forces_cos_one {N : ℕ} {b : ℝ} {a : ℂ → ℂ}
    (hb : |b| < 1) (ha : 0 < (a 0).im) (x : Fin N → ℝ)
    (hp : 1 - Complex.exp (-edgeTotalPhase (affineEdgeCenter b) a 0 x) = 0) :
    ∀ i, Real.cos (x i) = 1 := by
  have hnonneg (i : Fin N) : 0 ≤ (edgeAnglePhase (affineEdgeCenter b) a 0 (x i)).re :=
    edgeAnglePhase_boundary_re_nonneg (by simp [affineEdgeCenter]) hb ha _
  intro i
  by_contra hi
  have hpos : 0 < (edgeAnglePhase (affineEdgeCenter b) a 0 (x i)).re :=
    edgeAnglePhase_boundary_re_pos (b := b) (by simp [affineEdgeCenter]) ha
      (lt_of_le_of_ne (Real.cos_le_one _) hi)
  have hsum : 0 < (edgeTotalPhase (affineEdgeCenter b) a 0 x).re := by
    rw [edgeTotalPhase, Complex.re_sum]
    exact Finset.sum_pos' (fun j _ => hnonneg j) ⟨i, Finset.mem_univ _, hpos⟩
  exact phaseSiteFactor_denominator hsum hp

theorem boundary_rootProduct_of_cos_one {N : ℕ} {b : ℝ} {a : ℂ → ℂ}
    (x : Fin N → ℝ) (hx : ∀ i, Real.cos (x i) = 1) :
    Complex.exp (-edgeTotalPhase (affineEdgeCenter b) a 0 x) = upperEdgeRoot (b : ℂ) ^ N := by
  rw [edgeTotalPhase_exp_neg]
  have hr (i : Fin N) : edgeAngleRoot (affineEdgeCenter b) a 0 (x i) = upperEdgeRoot (b : ℂ) := by
    simp [edgeAngleRoot, edgeJointRoot, affineEdgeCenter, hx i]
  simp_rw [hr]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem boundary_pole_iff {N : ℕ} {b : ℝ} {a : ℂ → ℂ}
    (hb : |b| < 1) (ha : 0 < (a 0).im) (x : Fin N → ℝ) :
    1 - Complex.exp (-edgeTotalPhase (affineEdgeCenter b) a 0 x) = 0 ↔
      (∀ i, Real.cos (x i) = 1) ∧ upperEdgeRoot (b : ℂ) ^ N = 1 := by
  constructor
  · intro hp
    have hc := boundary_pole_forces_cos_one hb ha x hp
    refine ⟨hc, ?_⟩
    rw [boundary_rootProduct_of_cos_one x hc] at hp
    exact (sub_eq_zero.mp hp).symm
  · rintro ⟨hc, hp⟩
    rw [boundary_rootProduct_of_cos_one x hc, hp, sub_self]

/-- There is precisely one possible pole point in the actual independent
box, not several equal-amplitude collision charts. -/
theorem constrained_boundary_pole_iff {n : ℕ} {b : ℝ} {a : ℂ → ℂ}
    (hb : |b| < 1) (ha : 0 < (a 0).im) (q : Fin n → ℝ) (hq : q ∈ regularAngularBox n) :
    1 - Complex.exp (-edgeTotalPhase (affineEdgeCenter b) a 0 (flatConstrainedAngles q)) = 0 ↔
      q = 0 ∧ upperEdgeRoot (b : ℂ) ^ (n + 1) = 1 := by
  rw [boundary_pole_iff hb ha]
  constructor
  · rintro ⟨hc, hp⟩
    refine ⟨?_, hp⟩
    funext i
    have hi : Real.cos (q i) = 1 := by simpa [flatConstrainedAngles] using hc i.castSucc
    exact (Real.cos_eq_one_iff_of_lt_of_lt (by have := hq.1 i; linarith [Real.pi_pos])
      (by have := hq.2 i; linarith [Real.pi_pos])).mp hi
  · rintro ⟨rfl, hp⟩
    refine ⟨?_, hp⟩
    intro i
    exact Fin.lastCases (by simp [flatConstrainedAngles])
      (fun j => by simp [flatConstrainedAngles]) i

namespace RegularEdgeCompleteControl
variable {b : ℝ} {a : ℂ → ℂ} (d : RegularEdgeCompleteControl b a)

theorem jointDensity_analytic_of_denominator {N : ℕ} (x : Fin N → ℝ) {u : ℂ}
    (hu : u ∈ Metric.closedBall (0 : ℂ) d.phase.radius)
    (hG : 1 - Complex.exp (-edgeTotalPhase (affineEdgeCenter b) a u x) ≠ 0) :
    AnalyticAt ℂ (edgeJointDensity (affineEdgeCenter b) a) (u, complexAngles x) := by
  have hn := Metric.closedBall_subset_closedBall d.radius_le hu
  have hcos (i : Fin N) : Complex.cos (complexAngles x i) = (Real.cos (x i) : ℂ) := by
    simp [complexAngles, Complex.ofReal_cos]
  apply (d.numerator.jointNumerator_analytic hn ?_).mul
    ((phaseSiteFactor_analyticAt_of_denominator ?_).comp (d.phase.jointTotalPhase_analytic hu ?_))
  · intro i
    rw [hcos]
    exact Metric.self_subset_thickening d.numerator.cosineRadius_pos _
      (real_cos_mem_complexCosineInterval (x i))
  · rwa [edgeJointTotalPhase_real]
  · intro i
    rw [hcos]
    exact Metric.self_subset_thickening d.phase.cosineRadius_pos _
      (real_cos_mem_complexCosineInterval (x i))

include d in
theorem nonresonant_particle_analytic {n : ℕ}
    (hb : |b| < 1) (ha : 0 < (a 0).im) (hres : upperEdgeRoot (b : ℂ) ^ (n + 1) ≠ 1) :
    AnalyticAt ℂ (edgeParticleCoefficient (affineEdgeCenter b) a n) 0 := by
  apply analyticAt_const.mul
  have h := analyticAt_integral_of_joint_analytic
    (t := 0)
    (μ := regularAngularProbability n) (f := edgeJointDensity (affineEdgeCenter b) a)
    (g := fun q : Fin n → ℝ => complexAngles (flatConstrainedAngles q))
    (regularAngularBox_compact n) (regularAngularProbability_ae_mem n)
    ((complexAngles_continuous _).comp (flatConstrainedAngles_continuous n)) ?_
  · simpa only [edgeJointDensity_real] using h
  · intro q _
    apply d.jointDensity_analytic_of_denominator _ (Metric.mem_closedBall_self d.phase.radius_pos.le)
    intro hp
    exact hres ((boundary_pole_iff hb ha _).mp hp).2

end RegularEdgeCompleteControl
end
end IsingBulk.AnisoF002.RegularTail.C03
