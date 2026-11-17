import IsingBulk.AnisoF002.C03.IsotropicBoundaryRoot
import IsingBulk.AnisoF002.C03.IsotropicRetainedGaussianJets
import IsingBulk.AnisoF002.C03.IsotropicActualBumps

/-!
# Actual physical right-image inclusion and compatible inverse values

The physical phase is formed from the unique interior root. A continuous
extension is used only to apply compactness at its limiting boundary;
on the physical upper side the extension is proved equal to that phase.
The final image theorem concerns the actual physical root and returns the
identity U(S,v)=w, including near the branch and endpoint slivers.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

set_option maxHeartbeats 800000

open scoped Topology
open Filter Set Metric
open IsingBulk.AnisoF002.RegularTail

theorem upperBoundaryRoot_exp_arccos (x : ℝ) (hx : -1 < x) (hx1 : x ≤ 1) :
    upperBoundaryRoot x = Complex.exp (((-Real.arccos x : ℝ) : ℂ) * Complex.I) := by
  have hsq : x ^ 2 ≤ 1 := by nlinarith
  have hz : Real.sqrt (x ^ 2 - 1) = 0 := Real.sqrt_eq_zero_of_nonpos (by linarith)
  rw [Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg,
    Real.cos_arccos hx.le hx1, Real.sin_arccos]
  simp only [upperBoundaryRoot, hz, Complex.ofReal_zero, sub_zero, Complex.ofReal_neg]
  ring

theorem upperBoundaryPhase_eq_arccos (x : ℝ) (hx : -1 < x) (hx1 : x ≤ 1) :
    upperBoundaryPhase x = (Real.arccos x : ℂ) := by
  have hlo : -Real.pi < -Real.arccos x := by
    linarith [Real.arccos_lt_pi.mpr hx]
  have hhi : -Real.arccos x ≤ Real.pi := by linarith [Real.arccos_nonneg x, Real.pi_pos]
  unfold upperBoundaryPhase
  rw [upperBoundaryRoot_exp_arccos x hx hx1,
    Complex.log_exp (by simpa using hlo) (by simpa using hhi)]
  push_cast
  calc
    Complex.I * (-((Real.arccos x : ℂ)) * Complex.I) =
        -(Real.arccos x : ℂ) * (Complex.I ^ 2) := by ring
    _ = (Real.arccos x : ℂ) := by rw [Complex.I_sq]; ring

def upperRootContinuousExtension (W : ℂ) : ℂ :=
  if 0 < W.im then upperEdgeRoot W else upperBoundaryRoot W.re

theorem upperRootContinuousExtension_continuousAt_real (x : ℝ) (hx : -1 < x) :
    ContinuousAt upperRootContinuousExtension (x : ℂ) := by
  have he : upperRootContinuousExtension (x : ℂ) = upperBoundaryRoot x := by
    simp [upperRootContinuousExtension]
  change Tendsto upperRootContinuousExtension (𝓝 (x : ℂ)) (𝓝 (upperRootContinuousExtension (x : ℂ)))
  rw [he]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hbase : ∀ᶠ W : ℂ in 𝓝 (x : ℂ),
      dist (upperBoundaryRoot W.re) (upperBoundaryRoot x) < ε := by
    have hc : ContinuousAt (fun W : ℂ => upperBoundaryRoot W.re) (x : ℂ) :=
      (upperBoundaryRoot_continuous.comp Complex.continuous_re).continuousAt
    exact hc.tendsto.eventually (Metric.ball_mem_nhds (upperBoundaryRoot x) hε)
  filter_upwards [hbase, Metric.ball_mem_nhds (x : ℂ) (show 0 < ε ^ 2 / 2 by positivity)]
    with W hWbase hdist
  by_cases hW : 0 < W.im
  · rw [upperRootContinuousExtension, ite_eq_left hW, dist_eq_norm]
    have hb := upperEdgeRoot_boundary_holder x hx W hW
    rw [mem_ball, dist_eq_norm] at hdist
    nlinarith [norm_nonneg (upperEdgeRoot W - upperBoundaryRoot x)]
  · simpa only [upperRootContinuousExtension, ite_eq_right hW] using hWbase

def boundaryCompatiblePhase (W : ℂ) : ℂ := Complex.I * Complex.log (upperRootContinuousExtension W)

theorem boundaryCompatiblePhase_continuousAt_real (x : ℝ) (hx : -1 < x) :
    ContinuousAt boundaryCompatiblePhase (x : ℂ) := by
  have hs : upperRootContinuousExtension (x : ℂ) ∈ Complex.slitPlane := by
    simpa [upperRootContinuousExtension] using (upperBoundaryRoot_spec x hx).2.2.1
  exact continuousAt_const.mul
    ((continuousAt_clog hs).comp (upperRootContinuousExtension_continuousAt_real x hx))

theorem boundaryCompatiblePhase_eq_physical (W : ℂ) (hW : 0 < W.im) :
    boundaryCompatiblePhase W = upperPhysicalPhase W := by
  simp only [boundaryCompatiblePhase, upperRootContinuousExtension, ite_eq_left hW, upperPhysicalPhase]

theorem boundaryCompatiblePhase_ofReal (x : ℝ) :
    boundaryCompatiblePhase (x : ℂ) = upperBoundaryPhase x := by
  simp [boundaryCompatiblePhase, upperRootContinuousExtension, upperBoundaryPhase]

def physicalRegularCoordinate (q : ℂ × ℂ) : ℂ :=
  q.2 + upperPhysicalPhase (isotropicDispersion q)

def extendedRegularCoordinate (q : ℂ × ℂ) : ℂ :=
  q.2 + boundaryCompatiblePhase (isotropicDispersion q)

def physicalRegularCoordinateMap (q : ℂ × ℂ) : ℂ × ℂ := (q.1, physicalRegularCoordinate q)

def extendedRegularCoordinateMap (q : ℂ × ℂ) : ℂ × ℂ := (q.1, extendedRegularCoordinate q)

theorem extendedRegularCoordinateMap_eq_physical (q : ℂ × ℂ)
    (hW : 0 < (isotropicDispersion q).im) :
    extendedRegularCoordinateMap q = physicalRegularCoordinateMap q := by
  simp only [extendedRegularCoordinateMap, physicalRegularCoordinateMap, extendedRegularCoordinate,
    physicalRegularCoordinate, boundaryCompatiblePhase_eq_physical _ hW]

theorem extendedRegularCoordinateMap_continuousAt_real (S w : ℝ) (hS : 0 < S) :
    ContinuousAt extendedRegularCoordinateMap ((S : ℂ), (w : ℂ)) := by
  have hx : -1 < S - Real.cos w := by linarith [Real.cos_le_one w]
  have hW : isotropicDispersion ((S : ℂ), (w : ℂ)) = ((S - Real.cos w : ℝ) : ℂ) := by
    simp [isotropicDispersion]
  have hdisp : ContinuousAt isotropicDispersion ((S : ℂ), (w : ℂ)) := by
    unfold isotropicDispersion
    fun_prop
  have hphase : ContinuousAt (fun q => boundaryCompatiblePhase (isotropicDispersion q))
      ((S : ℂ), (w : ℂ)) := by
    have hc : ContinuousAt boundaryCompatiblePhase (isotropicDispersion ((S : ℂ), (w : ℂ))) := by
      rw [hW]
      exact boundaryCompatiblePhase_continuousAt_real _ hx
    exact hc.comp hdisp
  exact continuousAt_fst.prodMk (continuousAt_snd.add hphase)

theorem extendedRegularCoordinateMap_on_right_arc (S w : ℝ) (hS : 0 < S ∧ S < 2)
    (hw : w ∈ Icc (-rightBranchEndpoint S) 0) :
    extendedRegularCoordinateMap ((S : ℂ), (w : ℂ)) =
      ((S : ℂ), (rightArcCoordinate S w : ℂ)) := by
  have hx : -1 < S - Real.cos w := by linarith [hS.1, Real.cos_le_one w]
  have hx1 : S - Real.cos w ≤ 1 := by
    rw [← rightArcPhase_cos S w hS hw]
    exact Real.cos_le_one _
  have hW : isotropicDispersion ((S : ℂ), (w : ℂ)) = ((S - Real.cos w : ℝ) : ℂ) := by
    simp [isotropicDispersion]
  simp only [extendedRegularCoordinateMap, extendedRegularCoordinate, hW,
    boundaryCompatiblePhase_ofReal, upperBoundaryPhase_eq_arccos _ hx hx1]
  simp [rightArcCoordinate, rightArcPhase]

def rightAngularSegment (S : ℝ) : Set (ℂ × ℂ) :=
  {(S : ℂ)} ×ˢ (Complex.ofReal '' Icc (-rightBranchEndpoint S) 0)

theorem rightAngularSegment_isCompact (S : ℝ) : IsCompact (rightAngularSegment S) :=
  isCompact_singleton.prod (isCompact_Icc.image Complex.continuous_ofReal)

def inverseImageComparison (q : ℂ × ℂ) : ℂ :=
  minusCosineSecant
      (extendedRegularCoordinate q - explicitRightInverse (extendedRegularCoordinateMap q))
      (extendedRegularCoordinate q - q.2) -
    minusCosineSecant (explicitRightInverse (extendedRegularCoordinateMap q)) q.2

theorem inverseImageComparison_continuousAt (q : ℂ × ℂ)
    (hmap : ContinuousAt extendedRegularCoordinateMap q)
    (hU : AnalyticAt ℂ explicitRightInverse (extendedRegularCoordinateMap q)) :
    ContinuousAt inverseImageComparison q := by
  have hv : ContinuousAt extendedRegularCoordinate q := continuousAt_snd.comp hmap
  have hu := hU.continuousAt.comp hmap
  have hfirst : ContinuousAt
      (fun q => minusCosineSecant (extendedRegularCoordinate q - explicitRightInverse
        (extendedRegularCoordinateMap q)) (extendedRegularCoordinate q - q.2)) q :=
    (minusCosineSecant_analyticAt _).continuousAt.comp
      (f := fun q : ℂ × ℂ =>
        (extendedRegularCoordinate q - explicitRightInverse (extendedRegularCoordinateMap q),
          extendedRegularCoordinate q - q.2))
      ((hv.sub hu).prodMk (hv.sub continuousAt_snd))
  have hsecond : ContinuousAt
      (fun q => minusCosineSecant (explicitRightInverse (extendedRegularCoordinateMap q)) q.2) q :=
    (minusCosineSecant_analyticAt _).continuousAt.comp
      (f := fun q : ℂ × ℂ => (explicitRightInverse (extendedRegularCoordinateMap q), q.2))
      (hu.prodMk continuousAt_snd)
  exact hfirst.sub hsecond

theorem inverseImageComparison_on_right_arc (S w : ℝ) (hS : 0 < S ∧ S < 2)
    (hw : w ∈ Icc (-rightBranchEndpoint S) 0) :
    inverseImageComparison ((S : ℂ), (w : ℂ)) =
      explicitRightDenominator ((S : ℂ), (rightArcCoordinate S w : ℂ)) := by
  have hm := extendedRegularCoordinateMap_on_right_arc S w hS hw
  have hv : extendedRegularCoordinate ((S : ℂ), (w : ℂ)) = (rightArcCoordinate S w : ℂ) :=
    congrArg Prod.snd hm
  have hu := explicitRightInverse_on_right_arc S w hS hw
  simp only [inverseImageComparison, hm, hv, hu, minusCosineSecant_self,
    explicitRightDenominator]

/-- Actual right images enter any already chosen protected inverse
neighborhood, and the same existing explicit U recovers the actual
deformed angle. The tube includes short endpoint and branch slivers. -/
theorem exists_actual_right_image_tube (S r : ℝ) (hS : 0 < S ∧ S < 2) (hr : 0 < r) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ q ∈ cthickening δ (rightAngularSegment S),
      0 < (isotropicDispersion q).im →
      physicalRegularCoordinateMap q ∈ thickening r (rightParameterSegment S) ∧
        explicitRightInverse (physicalRegularCoordinateMap q) = q.2 := by
  let P : (ℂ × ℂ) → Prop := fun q =>
    extendedRegularCoordinateMap q ∈ thickening r (rightParameterSegment S) ∧
      Complex.cos (extendedRegularCoordinate q / 2) ≠ 0 ∧ inverseImageComparison q ≠ 0
  have hinside : rightAngularSegment S ⊆ interior {q | P q} := by
    rintro ⟨s, z⟩ ⟨hs, w, hw, hz⟩
    change s = (S : ℂ) at hs
    subst s
    change (w : ℂ) = z at hz
    subst z
    have hm := extendedRegularCoordinateMap_on_right_arc S w hS hw
    have hcont := extendedRegularCoordinateMap_continuousAt_real S w hS.1
    have hd := explicitRightInverse_data_on_arc S w hS hw
    have hU : AnalyticAt ℂ explicitRightInverse
        (extendedRegularCoordinateMap ((S : ℂ), (w : ℂ))) := by
      rw [hm]
      exact hd.1
    have htarget : extendedRegularCoordinateMap ((S : ℂ), (w : ℂ)) ∈
        thickening r (rightParameterSegment S) := by
      rw [hm]
      apply self_subset_thickening hr
      refine ⟨rfl, rightArcCoordinate S w, ?_, rfl⟩
      rw [← rightArcCoordinate_image S hS]
      exact ⟨w, hw, rfl⟩
    have hcos : ContinuousAt (fun q => Complex.cos (extendedRegularCoordinate q / 2))
        ((S : ℂ), (w : ℂ)) :=
      Complex.continuous_cos.continuousAt.comp ((continuousAt_snd.comp hcont).div_const 2)
    have hcos0 : Complex.cos (extendedRegularCoordinate ((S : ℂ), (w : ℂ)) / 2) ≠ 0 := by
      have hv : extendedRegularCoordinate ((S : ℂ), (w : ℂ)) = (rightArcCoordinate S w : ℂ) :=
        congrArg Prod.snd hm
      rw [hv]
      exact hd.2.1
    have hK : inverseImageComparison ((S : ℂ), (w : ℂ)) ≠ 0 := by
      rw [inverseImageComparison_on_right_arc S w hS hw]
      exact hd.2.2.1
    apply mem_interior_iff_mem_nhds.mpr
    filter_upwards [hcont.eventually (isOpen_thickening.mem_nhds htarget),
      hcos.eventually_ne hcos0, (inverseImageComparison_continuousAt _ hcont hU).eventually_ne hK]
      with q hq hqc hqK
    exact ⟨hq, hqc, hqK⟩
  obtain ⟨δ, hδ, hsub⟩ := (rightAngularSegment_isCompact S).exists_cthickening_subset_open
    isOpen_interior hinside
  refine ⟨δ, hδ, ?_⟩
  intro q hq hW
  have hd : P q := (interior_subset (s := {q | P q}) (hsub hq))
  have hm := extendedRegularCoordinateMap_eq_physical q hW
  have hv : extendedRegularCoordinate q = physicalRegularCoordinate q := congrArg Prod.snd hm
  refine ⟨by simpa only [hm] using hd.1, ?_⟩
  have hu := explicitRightInverse_dispersion (extendedRegularCoordinateMap q) hd.2.1
  have hw : Complex.cos q.2 + Complex.cos (extendedRegularCoordinate q - q.2) = q.1 := by
    rw [hv]
    change Complex.cos q.2 + Complex.cos
      ((q.2 + upperPhysicalPhase (isotropicDispersion q)) - q.2) = q.1
    rw [add_sub_cancel_left, upperPhysicalPhase_cos]
    simp only [isotropicDispersion]
    ring
  have hdiff := inverse_first_secant_difference q.1 (extendedRegularCoordinate q)
    (extendedRegularCoordinate q) (explicitRightInverse (extendedRegularCoordinateMap q)) q.2 hu hw
  have hprod : (explicitRightInverse (extendedRegularCoordinateMap q) - q.2) *
      inverseImageComparison q = 0 := by
    simpa only [inverseImageComparison, sub_self, zero_mul] using hdiff
  have he := sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right hd.2.2)
  simpa only [hm] using he

end IsingBulk.AnisoF002.Isotropic
