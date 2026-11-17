import IsingBulk.AnisoF002.C03.IsotropicOneSidedProtected
import IsingBulk.AnisoF002.C03.IsotropicRightHomotopy

/-!
# Actual whole one-sided deformation images and endpoint control

Every actual balanced homotopy point near the complete one-sided angular
interval enters a single preselected inverse neighborhood. Both endpoint
slivers are included; the constants precede N and all occupancy choices.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology
open Set Metric Filter

theorem extendedRegularCoordinateMap_on_oneSided (S w : ℝ) :
    extendedRegularCoordinateMap ((S : ℂ), (w : ℂ)) =
      ((S : ℂ), oneSidedBoundaryCoordinate S w) := by
  have hW : isotropicDispersion ((S : ℂ), (w : ℂ)) = ((S - Real.cos w : ℝ) : ℂ) := by
    simp [isotropicDispersion]
  simp only [extendedRegularCoordinateMap, extendedRegularCoordinate, hW,
    boundaryCompatiblePhase_ofReal, oneSidedBoundaryCoordinate]

def oneSidedAngularSegment (S : ℝ) : Set (ℂ × ℂ) :=
  {(S : ℂ)} ×ˢ (Complex.ofReal '' Icc (-Real.pi) 0)

theorem oneSidedAngularSegment_isCompact (S : ℝ) : IsCompact (oneSidedAngularSegment S) :=
  isCompact_singleton.prod (isCompact_Icc.image Complex.continuous_ofReal)

theorem exists_actual_oneSided_image_tube (S r : ℝ) (hS : 0 < S ∧ S < 2) (hr : 0 < r) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ q ∈ cthickening δ (oneSidedAngularSegment S),
      0 < (isotropicDispersion q).im →
      physicalRegularCoordinateMap q ∈ thickening r (oneSidedParameterArc S) ∧
        explicitRightInverse (physicalRegularCoordinateMap q) = q.2 := by
  let P : (ℂ × ℂ) → Prop := fun q =>
    extendedRegularCoordinateMap q ∈ thickening r (oneSidedParameterArc S) ∧
      Complex.cos (extendedRegularCoordinate q / 2) ≠ 0 ∧ inverseImageComparison q ≠ 0
  have hinside : oneSidedAngularSegment S ⊆ interior {q | P q} := by
    rintro ⟨s, z⟩ ⟨hs, w, hw, hz⟩
    change s = (S : ℂ) at hs
    subst s
    change (w : ℂ) = z at hz
    subst z
    have hm := extendedRegularCoordinateMap_on_oneSided S w
    have hv : extendedRegularCoordinate ((S : ℂ), (w : ℂ)) = oneSidedBoundaryCoordinate S w :=
      congrArg Prod.snd hm
    have hcont := extendedRegularCoordinateMap_continuousAt_real S w hS.1
    have hd := explicitRightInverse_on_oneSided_arc S w hS hw
    have hU : AnalyticAt ℂ explicitRightInverse
        (extendedRegularCoordinateMap ((S : ℂ), (w : ℂ))) := by
      rw [hm]
      exact hd.2.1
    have htarget : extendedRegularCoordinateMap ((S : ℂ), (w : ℂ)) ∈
        thickening r (oneSidedParameterArc S) := by
      rw [hm]
      exact self_subset_thickening hr _ ⟨rfl, w, hw, rfl⟩
    have hcos : ContinuousAt (fun q => Complex.cos (extendedRegularCoordinate q / 2))
        ((S : ℂ), (w : ℂ)) :=
      Complex.continuous_cos.continuousAt.comp ((continuousAt_snd.comp hcont).div_const 2)
    have hcos0 : Complex.cos (extendedRegularCoordinate ((S : ℂ), (w : ℂ)) / 2) ≠ 0 := by
      rw [hv]
      exact hd.2.2.1
    have hK : inverseImageComparison ((S : ℂ), (w : ℂ)) ≠ 0 := by
      have he : inverseImageComparison ((S : ℂ), (w : ℂ)) =
          explicitRightDenominator ((S : ℂ), oneSidedBoundaryCoordinate S w) := by
        simp only [inverseImageComparison, hm, hv, hd.1, minusCosineSecant_self,
          explicitRightDenominator]
      rw [he]
      exact hd.2.2.2
    apply mem_interior_iff_mem_nhds.mpr
    filter_upwards [hcont.eventually (isOpen_thickening.mem_nhds htarget),
      hcos.eventually_ne hcos0, (inverseImageComparison_continuousAt _ hcont hU).eventually_ne hK]
      with q hq hqc hqK
    exact ⟨hq, hqc, hqK⟩
  obtain ⟨δ, hδ, hsub⟩ := (oneSidedAngularSegment_isCompact S).exists_cthickening_subset_open
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

def oneSidedProductDomain (S r : ℝ) (N : ℕ) : Set (ℂ × (Fin N → ℂ)) :=
  {q | dist q.1 (S : ℂ) < r ∧ ∀ i, q.2 i ∈ thickening r (oneSidedCoordinateArc S)}

theorem oneSidedSingle_thickening_coordinates {S r : ℝ} {s v : ℂ}
    (h : (s, v) ∈ thickening r (oneSidedParameterArc S)) :
    dist s (S : ℂ) < r ∧ v ∈ thickening r (oneSidedCoordinateArc S) := by
  obtain ⟨⟨t, u⟩, htu, hd⟩ := mem_thickening_iff.mp h
  have ht : t = (S : ℂ) := htu.1
  have hu : u ∈ oneSidedCoordinateArc S := htu.2
  subst t
  have hd' : dist s (S : ℂ) < r ∧ dist v u < r := by
    simpa only [Prod.dist_eq, max_lt_iff] using hd
  exact ⟨hd'.1, mem_thickening_iff.mpr ⟨u, hu, hd'.2⟩⟩

/-- Complete actual one-sided image inclusion, with both endpoint
slivers and every homotopy time. No occupancy fraction is restricted. -/
theorem exists_actual_oneSided_homotopy_domain (S r : ℝ) (hS : 0 < S ∧ S < 2) (hr : 0 < r) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (N : ℕ), 0 < N →
      ∀ (s : ℂ), 0 < s.im → dist s (S : ℂ) < δ →
      ∀ (η τ ξ : ℝ), 0 < η → τ ∈ Icc 0 δ → ξ ∈ Icc 0 1 →
      ∀ θ : Fin N → ℝ, (∀ i, θ i ∈ Icc (-Real.pi - δ) δ) →
        actualHomotopyRegularTuple s η τ ξ θ ∈ oneSidedProductDomain S r N ∧
          ∀ i, explicitRightInverse
            (s, (actualHomotopyRegularTuple s η τ ξ θ).2 i) =
              actualHomotopyAngle η τ ξ θ i := by
  obtain ⟨δ₀, hδ₀, hδtube⟩ := exists_actual_oneSided_image_tube S r hS hr
  let δ := δ₀ / 4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨δ, hδ, ?_⟩
  intro N hN s hs hsnear η τ ξ hη hτ hξ θ hθ
  have hθtube : ∀ i : Fin N, (s, actualHomotopyAngle η τ ξ θ i) ∈
      cthickening δ₀ (oneSidedAngularSegment S) := by
    intro i
    obtain ⟨w, hw, hdw⟩ := interval_clamp_distance (-Real.pi) 0 δ (θ i)
      (neg_nonpos.mpr Real.pi_pos.le) hδ.le (by simpa only [zero_add] using hθ i)
    have hdisp := actual_balanced_homotopy_displacement η τ ξ hτ.1 hξ θ
      (by simpa using hN) i
    have hangle : dist (actualHomotopyAngle η τ ξ θ i) (w : ℂ) < δ₀ := by
      rw [dist_eq_norm]
      calc
        _ ≤ ‖actualHomotopyAngle η τ ξ θ i - (θ i : ℂ)‖ + ‖(θ i : ℂ) - (w : ℂ)‖ := by
          simpa only [dist_eq_norm] using
            dist_triangle (actualHomotopyAngle η τ ξ θ i) (θ i : ℂ) (w : ℂ)
        _ ≤ τ + δ := add_le_add hdisp
          (by simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using hdw)
        _ < δ₀ := by dsimp [δ] at *; linarith [hτ.2]
    apply thickening_subset_cthickening _ _
    apply mem_thickening_iff.mpr
    refine ⟨((S : ℂ), (w : ℂ)), ⟨rfl, w, hw, rfl⟩, ?_⟩
    simp only [Prod.dist_eq, max_lt_iff]
    exact ⟨hsnear.trans (by dsimp [δ]; linarith), hangle⟩
  have hdata : ∀ i : Fin N,
      physicalRegularCoordinateMap (s, actualHomotopyAngle η τ ξ θ i) ∈
          thickening r (oneSidedParameterArc S) ∧
        explicitRightInverse (physicalRegularCoordinateMap
          (s, actualHomotopyAngle η τ ξ θ i)) = actualHomotopyAngle η τ ξ θ i := by
    intro i
    exact hδtube _ (hθtube i) (actual_balanced_homotopy_sheet s hs η τ ξ hη hτ.1 hξ.1 θ i)
  have hcoord := fun i : Fin N => oneSidedSingle_thickening_coordinates (hdata i).1
  exact ⟨⟨(hcoord ⟨0, hN⟩).1, fun i => (hcoord i).2⟩, fun i => (hdata i).2⟩

end IsingBulk.AnisoF002.Isotropic
