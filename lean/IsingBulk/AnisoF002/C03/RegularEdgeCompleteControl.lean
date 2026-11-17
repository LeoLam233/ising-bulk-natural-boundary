import IsingBulk.AnisoF002.C03.RegularEdgeRetained
import IsingBulk.AnisoF002.C03.RegularEdgeAttenuation
import IsingBulk.AnisoF002.C03.RegularEdgeSiteKernel

/-!
# One constructed control for the entire regular-edge integrand

The numerator, the single logarithmic phase, and the inward attenuation
are placed on compatible disks.  This data is constructed from the edge
dispersion.  The complete density includes the rational site factor.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open Set Filter IsingBulk.AnisoF002.Isotropic
open scoped Topology BigOperators

def RegularEdgePhaseControl.restrict {c a : ℂ → ℂ} (d : RegularEdgePhaseControl c a)
    (r : ℝ) (hr : 0 < r) (hle : r ≤ d.radius) : RegularEdgePhaseControl c a where
  radius := r
  cosineRadius := d.cosineRadius
  phaseBound := d.phaseBound
  radius_pos := hr
  cosineRadius_pos := d.cosineRadius_pos
  phaseBound_pos := d.phaseBound_pos
  phase_analytic := fun t ht v hv => d.phase_analytic t
    (Metric.closedBall_subset_closedBall hle ht) v hv
  phase_bound := fun t ht q => d.phase_bound t (Metric.closedBall_subset_closedBall hle ht) q

structure RegularEdgeCompleteControl (b : ℝ) (a : ℂ → ℂ) where
  numerator : RegularEdgeControl (affineEdgeCenter b) a
  phase : RegularEdgePhaseControl (affineEdgeCenter b) a
  radius_le : phase.radius ≤ numerator.radius
  eps0 : ℝ
  kappa : ℝ
  eps0_pos : 0 < eps0
  kappa_pos : 0 < kappa
  inward_mem : ∀ eps : ℝ, 0 < eps → eps ≤ eps0 →
    (eps : ℂ) * Complex.I ∈ Metric.closedBall (0 : ℂ) (phase.radius / 4)
  coefficient_im_pos : ∀ eps : ℝ, 0 < eps → eps ≤ eps0 → 0 < (a ((eps : ℂ) * Complex.I)).im
  attenuation : ∀ eps : ℝ, 0 < eps → eps ≤ eps0 → ∀ q : ℝ, |q| ≤ Real.pi →
    kappa * (eps + q ^ 2) ≤ (edgeAnglePhase (affineEdgeCenter b) a ((eps : ℂ) * Complex.I) q).re

theorem exists_regular_edge_complete_control {a : ℂ → ℂ} {b : ℝ}
    (ha : AnalyticAt ℂ a 0) (hb : |b| < 1) (ha0 : 0 < (a 0).im) :
    Nonempty (RegularEdgeCompleteControl b a) := by
  obtain ⟨dn⟩ := exists_regular_edge_control (affineEdgeCenter_analytic b) ha
    (by simp [affineEdgeCenter]) hb ha0
  obtain ⟨dp, eps0, kappa, heps0, hkappa, hatt⟩ := exists_regular_edge_inward_attenuation ha hb ha0
  have hcoeff : ∀ᶠ t : ℂ in 𝓝 0, 0 < (a t).im :=
    (Complex.continuous_im.continuousAt.comp ha.continuousAt).eventually (Ioi_mem_nhds ha0)
  obtain ⟨r, hr, hcoeffr⟩ := Metric.eventually_nhds_iff.mp hcoeff
  let R := min dp.radius dn.radius
  have hR : 0 < R := lt_min dp.radius_pos dn.radius_pos
  let dp' := dp.restrict R hR (min_le_left _ _)
  let e := min eps0 (min (R / 4) (r / 2))
  have he : 0 < e := lt_min heps0 (lt_min (div_pos hR (by norm_num)) (half_pos hr))
  refine ⟨{
    numerator := dn
    phase := dp'
    radius_le := min_le_right _ _
    eps0 := e
    kappa := kappa
    eps0_pos := he
    kappa_pos := hkappa
    inward_mem := ?_
    coefficient_im_pos := ?_
    attenuation := ?_ }⟩
  · intro eps heps hepsle
    rw [Metric.mem_closedBall, dist_zero_right, inward_parameter_norm heps.le]
    exact hepsle.trans ((min_le_right _ _).trans (min_le_left _ _))
  · intro eps heps hepsle
    apply hcoeffr
    rw [dist_zero_right, inward_parameter_norm heps.le]
    exact (hepsle.trans ((min_le_right _ _).trans (min_le_right _ _))).trans_lt (half_lt_self hr)
  · intro eps heps hepsle q hq
    exact (hatt eps heps (hepsle.trans (min_le_left _ _))).2 q hq

def edgeFullDensity {N : ℕ} (c a : ℂ → ℂ) (t : ℂ) (x : Fin N → ℝ) : ℂ :=
  edgeFullNumerator c a t x * edgeSiteFactor c a t x

def edgeRetainedDensity {N : ℕ} (m : ℕ) (c a : ℂ → ℂ) (t : ℂ) (x : Fin (m + N) → ℝ) : ℂ :=
  edgeRetainedNumerator m c a t x * edgeSiteFactor c a t x

theorem edgeFullDensity_retained_factorization {m N : ℕ}
    (c a : ℂ → ℂ) (t : ℂ) (x : Fin (m + N) → ℝ) :
    edgeFullDensity c a t x =
      embeddedSineBlock m x * edgeRetainedDensity m c a t x := by
  unfold edgeFullDensity edgeRetainedDensity
  rw [edgeFullNumerator_retained_factorization]
  ring

theorem edgeFullDensity_iteratedDeriv_retained {m N : ℕ}
    (c a : ℂ → ℂ) (x : Fin (m + N) → ℝ) (j : ℕ) (t : ℂ) :
    iteratedDeriv j (fun u => edgeFullDensity c a u x) t =
      embeddedSineBlock m x *
        iteratedDeriv j (fun u => edgeRetainedDensity m c a u x) t := by
  have hf : (fun u => edgeFullDensity c a u x) = fun u =>
      embeddedSineBlock m x * edgeRetainedDensity m c a u x := by
    funext u
    exact edgeFullDensity_retained_factorization c a u x
  rw [hf, iteratedDeriv_const_mul_field]

namespace RegularEdgeCompleteControl
variable {b : ℝ} {a : ℂ → ℂ} (d : RegularEdgeCompleteControl b a)

theorem inward_anglePhase_pos {eps : ℝ} (he : 0 < eps) (he0 : eps ≤ d.eps0) (q : ℝ) :
    0 < (edgeAnglePhase (affineEdgeCenter b) a ((eps : ℂ) * Complex.I) q).re := by
  apply upperEdgePhase_re_pos
  rw [inward_dispersion_im]
  exact add_pos_of_pos_of_nonneg he (mul_nonneg (d.coefficient_im_pos eps he he0).le
    (sub_nonneg.mpr (Real.cos_le_one q)))

/-- Only the first m angles need principal representatives.  Every other
angle, including the constrained final angle, keeps its actual phase. -/
theorem totalPhase_retained_attenuation {m N : ℕ} {eps : ℝ}
    (he : 0 < eps) (he0 : eps ≤ d.eps0) (x : Fin (m + N) → ℝ)
    (hx : ∀ i : Fin m, |x (Fin.castAdd N i)| ≤ Real.pi) :
    d.kappa * (∑ i : Fin m, x (Fin.castAdd N i) ^ 2) ≤
      (edgeTotalPhase (affineEdgeCenter b) a ((eps : ℂ) * Complex.I) x).re := by
  have hfirst : ∀ i : Fin m,
      d.kappa * x (Fin.castAdd N i) ^ 2 ≤
        (edgeAnglePhase (affineEdgeCenter b) a ((eps : ℂ) * Complex.I) (x (Fin.castAdd N i))).re := by
    intro i
    have ha := d.attenuation eps he he0 _ (hx i)
    have hp := mul_nonneg d.kappa_pos.le he.le
    nlinarith
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin m))) => hfirst i)
  have hrest : 0 ≤ ∑ i : Fin N,
      (edgeAnglePhase (affineEdgeCenter b) a ((eps : ℂ) * Complex.I) (x (Fin.natAdd m i))).re :=
    Finset.sum_nonneg fun i _ => (d.inward_anglePhase_pos he he0 _).le
  unfold edgeTotalPhase
  rw [Complex.re_sum, Fin.sum_univ_add]
  rw [Finset.mul_sum]
  linarith

theorem siteDisk_subset_numerator {N : ℕ} {eta : ℝ} {t : ℂ}
    (hN : 0 < N) (he1 : eta ≤ 1)
    (ht : t ∈ Metric.closedBall (0 : ℂ) (d.phase.radius / 4)) :
    Metric.closedBall t (d.phase.siteRadius N eta) ⊆
      Metric.closedBall 0 d.numerator.radius := by
  exact (d.phase.siteDisk_subset_half hN he1 ht).trans
    (Metric.closedBall_subset_closedBall ((half_le_self d.phase.radius_pos.le).trans d.radius_le))

theorem retainedDensity_analytic {m N : ℕ} (x : Fin (m + N) → ℝ) {t : ℂ}
    (hn : t ∈ Metric.closedBall (0 : ℂ) d.numerator.radius)
    (hp : t ∈ Metric.closedBall (0 : ℂ) d.phase.radius)
    (hG : 0 < (edgeTotalPhase (affineEdgeCenter b) a t x).re) :
    AnalyticAt ℂ (fun u => edgeRetainedDensity m (affineEdgeCenter b) a u x) t :=
  (d.numerator.retainedNumerator_analytic m x hn).mul
    ((phaseSiteFactor_analyticAt hG).comp
      (f := fun u : ℂ => edgeTotalPhase (affineEdgeCenter b) a u x)
      (d.phase.totalPhase_parameter_analytic x hp))

/-- Cauchy is applied to the actual complete retained density on a disk
whose phase bound protects the rational pole. -/
theorem fullDensity_retained_jet_bound {m N : ℕ} (x : Fin (m + N) → ℝ)
    {t : ℂ} {eta E : ℝ} (hN : 0 < m + N) (he : 0 < eta) (he1 : eta ≤ 1)
    (ht : t ∈ Metric.closedBall (0 : ℂ) (d.phase.radius / 4))
    (hG : eta ≤ (edgeTotalPhase (affineEdgeCenter b) a t x).re)
    (hE : ∀ u ∈ Metric.closedBall (0 : ℂ) d.numerator.radius,
      ‖edgeRetainedNumerator m (affineEdgeCenter b) a u x‖ ≤ E) (j : ℕ) :
    ‖iteratedDeriv j (fun u => edgeFullDensity (affineEdgeCenter b) a u x) t‖ ≤
      retainedSineBlock (fun i : Fin m => x (Fin.castAdd N i)) *
        (j.factorial * (E * (8 / eta)) / (d.phase.siteRadius (m + N) eta) ^ j) := by
  rw [edgeFullDensity_iteratedDeriv_retained, norm_mul,
    embeddedSineBlock_norm_eq (Nat.le_add_right m N)]
  apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg fun _ _ => sq_nonneg _)
  apply Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le j (d.phase.siteRadius_pos hN he)
  · apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ (ne_of_gt (d.phase.siteRadius_pos hN he))]
    intro u hu
    have hprot := d.phase.siteDisk_phase_protected x hN he he1 ht hG hu
    exact (d.retainedDensity_analytic x (d.siteDisk_subset_numerator hN he1 ht hu)
      (Metric.closedBall_subset_closedBall (half_le_self d.phase.radius_pos.le)
        (d.phase.siteDisk_subset_half hN he1 ht hu)) (by linarith)).differentiableAt.differentiableWithinAt
  · intro u hu
    have hc := Metric.sphere_subset_closedBall hu
    have hprot := d.phase.siteDisk_phase_protected x hN he he1 ht hG hc
    unfold edgeRetainedDensity
    rw [norm_mul]
    exact mul_le_mul (hE u (d.siteDisk_subset_numerator hN he1 ht hc))
      (phaseSiteFactor_norm_le he he1 hprot) (norm_nonneg _) (le_trans (norm_nonneg _)
        (hE u (d.siteDisk_subset_numerator hN he1 ht hc)))

end RegularEdgeCompleteControl
end
end IsingBulk.AnisoF002.RegularTail.C03
