import IsingBulk.AnisoF002.C03.RegularEdgeCompleteControl
import IsingBulk.AnisoF002.C03.RegularParameterJets

/-!
# Joint complex angular neighborhoods for the complete density

The actual numerator and rational site factor are extended jointly in the
parameter and all complex angles.  Their restriction is exactly the real
cycle density.  Every fixed parameter derivative is therefore continuous
in the real angular variables on the inward path.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open Set IsingBulk.AnisoF002.Isotropic
open scoped Topology BigOperators

def complexAngles {N : ℕ} (x : Fin N → ℝ) : Fin N → ℂ := fun i => (x i : ℂ)

def edgeJointNumerator {N : ℕ} (c a : ℂ → ℂ) (p : ℂ × (Fin N → ℂ)) : ℂ :=
  edgePrefactor a p.1 ^ N *
    (∏ i, edgeOneBody c a (p.1, Complex.cos (p.2 i))) *
    ∏ ij ∈ indexPairs N,
      edgeSineCoefficient c a (p.1, Complex.cos (p.2 ij.1), Complex.cos (p.2 ij.2)) *
        Complex.sin ((p.2 ij.1 - p.2 ij.2) / 2) ^ 2

def edgeJointTotalPhase {N : ℕ} (c a : ℂ → ℂ) (p : ℂ × (Fin N → ℂ)) : ℂ :=
  ∑ i, edgeJointPhase c a (p.1, Complex.cos (p.2 i))

def edgeJointDensity {N : ℕ} (c a : ℂ → ℂ) (p : ℂ × (Fin N → ℂ)) : ℂ :=
  edgeJointNumerator c a p * phaseSiteFactor (edgeJointTotalPhase c a p)

theorem edgeJointNumerator_real {N : ℕ} (c a : ℂ → ℂ) (t : ℂ) (x : Fin N → ℝ) :
    edgeJointNumerator c a (t, complexAngles x) = edgeFullNumerator c a t x := by
  unfold edgeJointNumerator edgeFullNumerator branchFullNumerator
  congr 1
  · congr 1
    apply Finset.prod_congr rfl
    intro i _
    simp [edgeOneBody, branchOneBody, edgeAngleRoot, complexAngles, Complex.ofReal_cos]
  · apply Finset.prod_congr rfl
    intro ij _
    rw [branchCanceledPair_eq_real_sine]
    simp [edgeSineCoefficient, edgeAngleRoot, complexAngles, Complex.ofReal_cos,
      Complex.ofReal_sin, Complex.ofReal_pow, Complex.ofReal_sub, Complex.ofReal_div]

theorem edgeJointTotalPhase_real {N : ℕ} (c a : ℂ → ℂ) (t : ℂ) (x : Fin N → ℝ) :
    edgeJointTotalPhase c a (t, complexAngles x) = edgeTotalPhase c a t x := by
  simp only [edgeJointTotalPhase, edgeTotalPhase, edgeAnglePhase, complexAngles, Complex.ofReal_cos]

theorem edgeJointDensity_real {N : ℕ} (c a : ℂ → ℂ) (t : ℂ) (x : Fin N → ℝ) :
    edgeJointDensity c a (t, complexAngles x) = edgeFullDensity c a t x := by
  rw [edgeJointDensity, edgeJointNumerator_real, edgeJointTotalPhase_real]
  rfl

theorem analyticAt_angle_coordinate {N : ℕ} (i : Fin N) (p : ℂ × (Fin N → ℂ)) :
    AnalyticAt ℂ (fun q : ℂ × (Fin N → ℂ) => q.2 i) p := by
  let L : (Fin N → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj i
  exact (L.analyticAt p.2).comp (f := fun q : ℂ × (Fin N → ℂ) => q.2) analyticAt_snd

namespace RegularEdgeControl
variable {c a : ℂ → ℂ} (d : RegularEdgeControl c a)

theorem jointNumerator_analytic {N : ℕ} {p : ℂ × (Fin N → ℂ)}
    (ht : p.1 ∈ Metric.closedBall (0 : ℂ) d.radius)
    (hx : ∀ i, Complex.cos (p.2 i) ∈ Metric.thickening d.cosineRadius complexCosineInterval) :
    AnalyticAt ℂ (edgeJointNumerator c a) p := by
  have hc (i : Fin N) : AnalyticAt ℂ (fun q : ℂ × (Fin N → ℂ) => Complex.cos (q.2 i)) p :=
    Complex.analyticAt_cos.comp (analyticAt_angle_coordinate i p)
  have hone (i : Fin N) : AnalyticAt ℂ
      (fun q : ℂ × (Fin N → ℂ) => edgeOneBody c a (q.1, Complex.cos (q.2 i))) p := by
    have hprot := d.protected_pairs p.1 ht _ (hx i) _ (hx i)
    exact (edgeOneBody_analyticAt hprot.1 hprot.2.2.1).comp
      (f := fun q : ℂ × (Fin N → ℂ) => (q.1, Complex.cos (q.2 i)))
      (analyticAt_fst.prod (hc i))
  have hpair (ij : Fin N × Fin N) : AnalyticAt ℂ
      (fun q : ℂ × (Fin N → ℂ) =>
        edgeSineCoefficient c a (q.1, Complex.cos (q.2 ij.1), Complex.cos (q.2 ij.2)) *
          Complex.sin ((q.2 ij.1 - q.2 ij.2) / 2) ^ 2) p := by
    have hs := edgeSineCoefficient_analyticAt (d.coefficient_analytic p.1 ht)
      (d.protected_pairs p.1 ht _ (hx ij.1) _ (hx ij.2))
    exact (hs.comp
      (f := fun q : ℂ × (Fin N → ℂ) => (q.1, Complex.cos (q.2 ij.1), Complex.cos (q.2 ij.2)))
      (analyticAt_fst.prod ((hc ij.1).prod (hc ij.2)))).mul
      ((Complex.analyticAt_sin.comp (((analyticAt_angle_coordinate ij.1 p).sub
        (analyticAt_angle_coordinate ij.2 p)).div_const)).pow 2)
  exact (((d.prefactor_analytic p.1 ht).comp analyticAt_fst).pow N).mul
    (Finset.univ.analyticAt_fun_prod fun i _ => hone i) |>.mul
      ((indexPairs N).analyticAt_fun_prod fun ij _ => hpair ij)

end RegularEdgeControl

namespace RegularEdgePhaseControl
variable {c a : ℂ → ℂ} (d : RegularEdgePhaseControl c a)

theorem jointTotalPhase_analytic {N : ℕ} {p : ℂ × (Fin N → ℂ)}
    (ht : p.1 ∈ Metric.closedBall (0 : ℂ) d.radius)
    (hx : ∀ i, Complex.cos (p.2 i) ∈ Metric.thickening d.cosineRadius complexCosineInterval) :
    AnalyticAt ℂ (edgeJointTotalPhase c a) p := by
  exact Finset.univ.analyticAt_fun_sum fun i _ =>
    (d.phase_analytic p.1 ht _ (hx i)).comp
      (f := fun q : ℂ × (Fin N → ℂ) => (q.1, Complex.cos (q.2 i)))
      (analyticAt_fst.prod (Complex.analyticAt_cos.comp (analyticAt_angle_coordinate i p)))

end RegularEdgePhaseControl

namespace RegularEdgeCompleteControl
variable {b : ℝ} {a : ℂ → ℂ} (d : RegularEdgeCompleteControl b a)

theorem inward_totalPhase_pos {N : ℕ} (hN : 0 < N) {eps : ℝ}
    (he : 0 < eps) (he0 : eps ≤ d.eps0) (x : Fin N → ℝ) :
    0 < (edgeTotalPhase (affineEdgeCenter b) a ((eps : ℂ) * Complex.I) x).re := by
  rw [edgeTotalPhase, Complex.re_sum]
  exact Finset.sum_pos (fun i _ => d.inward_anglePhase_pos he he0 (x i))
    (Finset.univ_nonempty_iff.mpr ⟨⟨0, hN⟩⟩)

theorem jointDensity_analytic_inward {N : ℕ} (hN : 0 < N) {eps : ℝ}
    (he : 0 < eps) (he0 : eps ≤ d.eps0) (x : Fin N → ℝ) :
    AnalyticAt ℂ (edgeJointDensity (affineEdgeCenter b) a)
      ((eps : ℂ) * Complex.I, complexAngles x) := by
  have hp := d.inward_mem eps he he0
  have hp' : (eps : ℂ) * Complex.I ∈ Metric.closedBall (0 : ℂ) d.phase.radius :=
    Metric.closedBall_subset_closedBall (by linarith [d.phase.radius_pos]) hp
  have hn := Metric.closedBall_subset_closedBall d.radius_le hp'
  have hcos (i : Fin N) : Complex.cos (complexAngles x i) = (Real.cos (x i) : ℂ) := by
    simp [complexAngles, Complex.ofReal_cos]
  apply (d.numerator.jointNumerator_analytic hn ?_).mul
    ((phaseSiteFactor_analyticAt ?_).comp (d.phase.jointTotalPhase_analytic hp' ?_))
  · intro i
    rw [hcos]
    exact Metric.self_subset_thickening d.numerator.cosineRadius_pos _
      (real_cos_mem_complexCosineInterval (x i))
  · rw [edgeJointTotalPhase_real]
    exact d.inward_totalPhase_pos hN he he0 x
  · intro i
    rw [hcos]
    exact Metric.self_subset_thickening d.phase.cosineRadius_pos _
      (real_cos_mem_complexCosineInterval (x i))

theorem fullDensity_jet_continuous_inward {N : ℕ} (hN : 0 < N) {eps : ℝ}
    (he : 0 < eps) (he0 : eps ≤ d.eps0) (j : ℕ) :
    Continuous (fun x : Fin N → ℝ =>
      iteratedDeriv j (fun u => edgeFullDensity (affineEdgeCenter b) a u x)
        ((eps : ℂ) * Complex.I)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  have hm : ContinuousAt (fun y : Fin N → ℝ =>
      ((eps : ℂ) * Complex.I, complexAngles y)) x := by
    exact continuousAt_const.prodMk (continuous_pi fun i =>
      Complex.continuous_ofReal.comp (continuous_apply i)).continuousAt
  have hc := (parameterIteratedDeriv_analyticAt
    (d.jointDensity_analytic_inward hN he he0 x) j).continuousAt.comp
      (f := fun y : Fin N → ℝ => ((eps : ℂ) * Complex.I, complexAngles y)) hm
  simpa only [Function.comp_def, edgeJointDensity_real] using hc

end RegularEdgeCompleteControl
end
end IsingBulk.AnisoF002.RegularTail.C03
