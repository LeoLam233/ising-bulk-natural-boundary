import IsingBulk.AnisoF002.C03.RegularNonresonant

/-!
# The complete off-collision integral is analytic at a regular edge

The exterior of one fixed collision ball is a compact subset of the
actual independent-angle box.  The exact pole-locus theorem proves the
complete density analytic there, even at a resonant particle number.
The physical inward coefficient splits exactly into this analytic
exterior and its local collision integral.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open Set MeasureTheory
open scoped Topology

def collisionExterior (n : ℕ) (delta : ℝ) : Set (Fin n → ℝ) :=
  regularAngularBox n \ Metric.ball 0 delta

theorem collisionExterior_compact (n : ℕ) (delta : ℝ) : IsCompact (collisionExterior n delta) :=
  (regularAngularBox_compact n).diff Metric.isOpen_ball

def edgeOffCollisionCoefficient (c a : ℂ → ℂ) (n : ℕ) (delta : ℝ) (t : ℂ) : ℂ :=
  ((n + 1).factorial : ℂ)⁻¹ * ∫ q in collisionExterior n delta,
    edgeFullDensity c a t (flatConstrainedAngles q) ∂regularAngularProbability n

def edgeLocalCollisionCoefficient (c a : ℂ → ℂ) (n : ℕ) (delta : ℝ) (t : ℂ) : ℂ :=
  ((n + 1).factorial : ℂ)⁻¹ * ∫ q in Metric.ball 0 delta,
    edgeFullDensity c a t (flatConstrainedAngles q) ∂regularAngularProbability n

namespace RegularEdgeCompleteControl
variable {b : ℝ} {a : ℂ → ℂ} (d : RegularEdgeCompleteControl b a)

include d in
theorem offCollisionCoefficient_analytic {n : ℕ} {delta : ℝ}
    (hb : |b| < 1) (ha : 0 < (a 0).im) (hd : 0 < delta) :
    AnalyticAt ℂ (edgeOffCollisionCoefficient (affineEdgeCenter b) a n delta) 0 := by
  apply analyticAt_const.mul
  have hK := collisionExterior_compact n delta
  have h := analyticAt_integral_of_joint_analytic
    (t := 0) (μ := (regularAngularProbability n).restrict (collisionExterior n delta))
    (f := edgeJointDensity (affineEdgeCenter b) a)
    (g := fun q : Fin n → ℝ => complexAngles (flatConstrainedAngles q))
    hK (self_mem_ae_restrict hK.measurableSet)
    ((complexAngles_continuous _).comp (flatConstrainedAngles_continuous n)) ?_
  · simpa only [edgeJointDensity_real] using h
  · intro q hq
    apply d.jointDensity_analytic_of_denominator _ (Metric.mem_closedBall_self d.phase.radius_pos.le)
    intro hp
    have hz := ((constrained_boundary_pole_iff hb ha q hq.1).mp hp).1
    exact hq.2 (hz ▸ Metric.mem_ball_self hd)

theorem particleCoefficient_collision_decomposition (n : ℕ) (delta : ℝ) {eps : ℝ}
    (he : 0 < eps) (he0 : eps ≤ d.eps0) :
    edgeParticleCoefficient (affineEdgeCenter b) a n ((eps : ℂ) * Complex.I) =
      edgeLocalCollisionCoefficient (affineEdgeCenter b) a n delta ((eps : ℂ) * Complex.I) +
      edgeOffCollisionCoefficient (affineEdgeCenter b) a n delta ((eps : ℂ) * Complex.I) := by
  have hf : Integrable (fun q : Fin n → ℝ =>
      edgeFullDensity (affineEdgeCenter b) a ((eps : ℂ) * Complex.I) (flatConstrainedAngles q))
        (regularAngularProbability n) := by
    apply integrable_of_carried_compact (regularAngularBox_compact n) (regularAngularProbability_ae_mem n)
    exact ((d.fullDensity_jet_continuous_inward (by omega : 0 < n + 1) he he0 0).comp
      (flatConstrainedAngles_continuous n)).continuousOn
  have hm : (regularAngularProbability n).restrict (Metric.ball (0 : Fin n → ℝ) delta)ᶜ =
      (regularAngularProbability n).restrict (collisionExterior n delta) := by
    apply Measure.restrict_congr_set
    filter_upwards [regularAngularProbability_ae_mem n] with q hq
    simp [collisionExterior, hq]
  have hs := integral_add_compl (μ := regularAngularProbability n)
    (s := Metric.ball (0 : Fin n → ℝ) delta) Metric.isOpen_ball.measurableSet hf
  rw [hm] at hs
  unfold edgeParticleCoefficient edgeLocalCollisionCoefficient edgeOffCollisionCoefficient
  rw [← mul_add, hs]

end RegularEdgeCompleteControl
end
end IsingBulk.AnisoF002.RegularTail.C03
