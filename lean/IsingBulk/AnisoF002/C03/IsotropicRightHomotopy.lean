import IsingBulk.AnisoF002.C03.IsotropicRightImage
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

/-!
# The actual balanced right homotopy enters the protected jet domain

The homotopy uses the constructed smooth periodic bumps and all particle
populations. A single deformation size, chosen before N and the retained
set, includes short slivers at both ends of the right angular interval.
The actual physical phase is used throughout. The filled pair is also
identified with the original canceled physical pair on this homotopy.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators
open Set Metric
open IsingBulk.AnisoF002.RegularTail

theorem interval_clamp_distance (a b t x : ℝ) (hab : a ≤ b) (ht : 0 ≤ t)
    (hx : x ∈ Icc (a - t) (b + t)) :
    ∃ y ∈ Icc a b, |x - y| ≤ t := by
  by_cases hxa : x < a
  · refine ⟨a, ⟨le_rfl, hab⟩, ?_⟩
    rw [abs_of_neg (sub_neg.mpr hxa)]
    linarith [hx.1]
  · by_cases hxb : b < x
    · refine ⟨b, ⟨hab, le_rfl⟩, ?_⟩
      rw [abs_of_pos (sub_pos.mpr hxb)]
      linarith [hx.2]
    · exact ⟨x, ⟨le_of_not_gt hxa, le_of_not_gt hxb⟩, by simpa using ht⟩

def actualHomotopyAngle {ι : Type*} [Fintype ι] (η τ ξ : ℝ) (θ : ι → ℝ) (i : ι) : ℂ :=
  balancedHomotopyCoordinate τ θ (fun j => upperPeriodicBump η (θ j))
    (fun j => lowerPeriodicBump η (θ j)) ξ i

def actualHomotopyRegularTuple {N : ℕ} (s : ℂ) (η τ ξ : ℝ) (θ : Fin N → ℝ) :
    ℂ × (Fin N → ℂ) :=
  (s, fun i => physicalRegularCoordinate (s, actualHomotopyAngle η τ ξ θ i))

theorem rightSingle_thickening_coordinates {S r : ℝ} {s v : ℂ}
    (h : (s, v) ∈ thickening r (rightParameterSegment S)) :
    dist s (S : ℂ) < r ∧ v ∈ thickening r (rightCoordinateInterval S) := by
  obtain ⟨⟨t, u⟩, htu, hd⟩ := mem_thickening_iff.mp h
  have ht : t = (S : ℂ) := htu.1
  have hu : u ∈ rightCoordinateInterval S := htu.2
  subst t
  have hd' : dist s (S : ℂ) < r ∧ dist v u < r := by
    simpa only [Prod.dist_eq, max_lt_iff] using hd
  exact ⟨hd'.1, mem_thickening_iff.mpr ⟨u, hu, hd'.2⟩⟩

/-- N-independent actual image inclusion, with endpoint and branch
slivers and every homotopy time. The inverse value is the actual angle. -/
theorem exists_actual_right_homotopy_domain (S r : ℝ) (hS : 0 < S ∧ S < 2) (hr : 0 < r) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (N : ℕ), 0 < N →
      ∀ (s : ℂ), 0 < s.im → dist s (S : ℂ) < δ →
      ∀ (η τ ξ : ℝ), 0 < η → τ ∈ Icc 0 δ → ξ ∈ Icc 0 1 →
      ∀ θ : Fin N → ℝ,
        (∀ i, θ i ∈ Icc (-rightBranchEndpoint S - δ) δ) →
        actualHomotopyRegularTuple s η τ ξ θ ∈ rightProductDomain S r N ∧
          ∀ i, explicitRightInverse
            (s, (actualHomotopyRegularTuple s η τ ξ θ).2 i) =
              actualHomotopyAngle η τ ξ θ i := by
  obtain ⟨δ₀, hδ₀, hδtube⟩ := exists_actual_right_image_tube S r hS hr
  let δ := δ₀ / 4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨δ, hδ, ?_⟩
  intro N hN s hs hsnear η τ ξ hη hτ hξ θ hθ
  have hθtube : ∀ i : Fin N, (s, actualHomotopyAngle η τ ξ θ i) ∈
      cthickening δ₀ (rightAngularSegment S) := by
    intro i
    obtain ⟨w, hw, hdw⟩ := interval_clamp_distance (-rightBranchEndpoint S) 0 δ (θ i)
      (neg_nonpos.mpr (rightBranchEndpoint_pos S hS.2).le) hδ.le
      (by simpa only [zero_add] using hθ i)
    have hdisp := actual_balanced_homotopy_displacement η τ ξ hτ.1 hξ θ
      (by simpa using hN) i
    have hangle : dist (actualHomotopyAngle η τ ξ θ i) (w : ℂ) < δ₀ := by
      rw [dist_eq_norm]
      calc
        _ ≤ ‖actualHomotopyAngle η τ ξ θ i - (θ i : ℂ)‖ + ‖(θ i : ℂ) - (w : ℂ)‖ :=
          by simpa only [dist_eq_norm] using
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
          thickening r (rightParameterSegment S) ∧
        explicitRightInverse (physicalRegularCoordinateMap
          (s, actualHomotopyAngle η τ ξ θ i)) = actualHomotopyAngle η τ ξ θ i := by
    intro i
    exact hδtube _ (hθtube i) (actual_balanced_homotopy_sheet s hs η τ ξ hη hτ.1 hξ.1 θ i)
  have hcoord := fun i : Fin N => rightSingle_thickening_coordinates (hdata i).1
  refine ⟨⟨(hcoord ⟨0, hN⟩).1, fun i => (hcoord i).2⟩, fun i => (hdata i).2⟩

theorem upperPhysicalPhase_im_neg (W : ℂ) (hW : 0 < W.im) :
    (upperPhysicalPhase W).im < 0 := by
  simp only [upperPhysicalPhase, Complex.mul_im, Complex.I_re, zero_mul,
    Complex.I_im, one_mul, zero_add, Complex.log_re]
  exact Real.log_neg (norm_pos_iff.mpr (upperEdgeRoot_ne_zero W)) (upperEdgeRoot_norm_lt_one hW)

theorem upperPhysicalPhase_pair_sine_ne_zero (W V : ℂ) (hW : 0 < W.im) (hV : 0 < V.im) :
    Complex.sin ((upperPhysicalPhase W + upperPhysicalPhase V) / 2) ≠ 0 := by
  intro hz
  obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp hz
  have hi := congrArg Complex.im hk
  have hWi := upperPhysicalPhase_im_neg W hW
  have hVi := upperPhysicalPhase_im_neg V hV
  have he : (((k : ℂ) * (Real.pi : ℂ))).im = 0 := by simp
  rw [he] at hi
  have hleft : ((upperPhysicalPhase W + upperPhysicalPhase V) / 2).im =
      ((upperPhysicalPhase W).im + (upperPhysicalPhase V).im) / 2 := by simp
  rw [hleft] at hi
  linarith

/-- The filled pair on the actual physical sheet is exactly the original
canceled pair, with the roots of the physical quadratic and the actual
deformed angular exponentials. -/
theorem inversePairFilled_physical_identification (s wa wb : ℂ)
    (ha : 0 < (isotropicDispersion (s, wa)).im)
    (hb : 0 < (isotropicDispersion (s, wb)).im)
    (hUa : explicitRightInverse (physicalRegularCoordinateMap (s, wa)) = wa)
    (hUb : explicitRightInverse (physicalRegularCoordinateMap (s, wb)) = wb) :
    inversePairFilled explicitRightInverse
      (s, physicalRegularCoordinate (s, wa), physicalRegularCoordinate (s, wb)) =
      canceledPair 1 (isotropicInteriorRoot (s, wa)) (isotropicInteriorRoot (s, wb))
        (Complex.exp (wa * Complex.I)) (Complex.exp (wb * Complex.I)) := by
  have hpa : physicalRegularCoordinate (s, wa) - wa =
      upperPhysicalPhase (isotropicDispersion (s, wa)) := by
    dsimp only [physicalRegularCoordinate]
    ring
  have hpb : physicalRegularCoordinate (s, wb) - wb =
      upperPhysicalPhase (isotropicDispersion (s, wb)) := by
    dsimp only [physicalRegularCoordinate]
    ring
  change explicitRightInverse (s, physicalRegularCoordinate (s, wa)) = wa at hUa
  change explicitRightInverse (s, physicalRegularCoordinate (s, wb)) = wb at hUb
  rw [inversePairFilled, hUa, hUb, hpa, hpb,
    ite_eq_right (upperPhysicalPhase_pair_sine_ne_zero _ _ ha hb)]
  dsimp only [inversePairOriginal]
  rw [hUa, hUb, hpa, hpb]
  rw [← canceledPair_isotropic_phase wa wb, upperPhysicalPhase_exp, upperPhysicalPhase_exp]
  rfl

/-- All fixed joint jets of the complete retained numerator on the
actual balanced right image. The size and Gaussian constants precede
particle count, homotopy time, and the retained collision set. -/
theorem exists_actual_right_homotopy_retained_jets (S : ℝ) (hS : 0 < S ∧ S < 2) :
    ∃ δ κ C M : ℝ, 0 < δ ∧ 0 < κ ∧ 0 < C ∧ 0 < M ∧
      ∀ k : ℕ, ∃ Ck : ℝ, 0 < Ck ∧
      ∀ (N : ℕ), 0 < N →
      ∀ (R : Finset (Fin N × Fin N)), R ⊆ indexPairs N →
      ∀ (s : ℂ), 0 < s.im → dist s (S : ℂ) < δ →
      ∀ (η τ ξ : ℝ), 0 < η → τ ∈ Icc 0 δ → ξ ∈ Icc 0 1 →
      ∀ θ : Fin N → ℝ,
        (∀ i, θ i ∈ Icc (-rightBranchEndpoint S - δ) δ) →
        ‖iteratedFDeriv ℂ k (retainedRegularNumerator R)
          (actualHomotopyRegularTuple s η τ ξ θ)‖ ≤
          Ck * C ^ N * M ^ R.card * Real.exp (-κ * (N : ℝ) ^ 2 + (1 / 2 : ℝ) * N) := by
  obtain ⟨r, κ, C, M, hr, hκ, hC, hM, hjets⟩ :=
    exists_actual_retainedNumerator_all_joint_jets S hS
  obtain ⟨δ, hδ, hdomain⟩ := exists_actual_right_homotopy_domain S r hS hr
  refine ⟨δ, κ, C, M, hδ, hκ, hC, hM, ?_⟩
  intro k
  obtain ⟨Ck, hCk, hk⟩ := hjets k
  refine ⟨Ck, hCk, ?_⟩
  intro N hN R hR s hs hsnear η τ ξ hη hτ hξ θ hθ
  exact hk N R hR _ (hdomain N hN s hs hsnear η τ ξ hη hτ hξ θ hθ).1

end IsingBulk.AnisoF002.Isotropic
