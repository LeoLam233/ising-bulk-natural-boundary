import IsingBulk.AnisoF002.Isotropic.InverseCurvature
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# The actual real right arc of the isotropic dispersion

This implements the right-arc coordinate construction in frozen F002
Lemma 7.3.  The coordinate is strictly increasing, its exact image is
`[-b,b]`, and this image lies strictly inside `(-2α,2α)`.  Every point of
the actual arc therefore supplies the correct nonzero unsquared inverse
denominator and the constructed analytic inverse with positive curvature.

Common complex patching and uniform inclusion of all deformed images are
not conclusions of this file.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology
open Filter Set

def rightBranchEndpoint (S : ℝ) : ℝ := Real.arccos (S - 1)

def rightArcPhase (S w : ℝ) : ℝ := Real.arccos (S - Real.cos w)

def rightArcCoordinate (S w : ℝ) : ℝ := w + rightArcPhase S w

theorem rightBranchEndpoint_pos (S : ℝ) (hS : S < 2) :
    0 < rightBranchEndpoint S :=
  Real.arccos_pos.mpr (by linarith)

theorem rightBranchEndpoint_lt_pi (S : ℝ) (hS : 0 < S) :
    rightBranchEndpoint S < Real.pi :=
  Real.arccos_lt_pi.mpr (by linarith)

theorem rightBranchEndpoint_cos (S : ℝ) (hS : 0 < S ∧ S < 2) :
    Real.cos (rightBranchEndpoint S) = S - 1 :=
  Real.cos_arccos (by linarith [hS.1]) (by linarith [hS.2])

/-- The spectral edge endpoint lies strictly inside twice the Nickel angle. -/
theorem rightBranchEndpoint_lt_two_angle (S : ℝ) (hS : 0 < S ∧ S < 2) :
    rightBranchEndpoint S < 2 * Real.arccos (S / 2) := by
  by_contra h
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Real.arccos_nonneg (S / 2)))
    (Real.arccos_le_pi (S - 1)) (le_of_not_gt h)
  change Real.cos (rightBranchEndpoint S) ≤ Real.cos (2 * Real.arccos (S / 2)) at hc
  rw [rightBranchEndpoint_cos S hS, Real.cos_two_mul,
    Real.cos_arccos (by linarith [hS.1]) (by linarith [hS.2])] at hc
  nlinarith [mul_pos hS.1 (sub_pos.mpr hS.2)]

theorem rightArcPhase_cos (S w : ℝ) (hS : 0 < S ∧ S < 2)
    (hw : w ∈ Icc (-rightBranchEndpoint S) 0) :
    Real.cos (rightArcPhase S w) = S - Real.cos w := by
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi
    (x := -w) (y := rightBranchEndpoint S)
    (neg_nonneg.mpr hw.2) (Real.arccos_le_pi (S - 1)) (by linarith [hw.1])
  rw [rightBranchEndpoint_cos S hS, Real.cos_neg] at hc
  exact Real.cos_arccos (by linarith [Real.cos_le_one w, hS.1]) (by linarith)

theorem rightArcPhase_range (S w : ℝ) (hS : 0 < S) :
    0 ≤ rightArcPhase S w ∧ rightArcPhase S w < Real.pi := by
  refine ⟨Real.arccos_nonneg _, Real.arccos_lt_pi.mpr ?_⟩
  linarith [Real.cos_le_one w]

/-- The complete real coordinate is injective even before restricting to
the physical right-arc subinterval. -/
theorem rightArcCoordinate_strictMonoOn (S : ℝ) :
    StrictMonoOn (rightArcCoordinate S) (Icc (-Real.pi) 0) := by
  intro x hx y hy hxy
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi (x := -y) (y := -x)
    (neg_nonneg.mpr hy.2) (by linarith [hx.1]) (by linarith)
  simp only [Real.cos_neg] at hc
  have hg : rightArcPhase S x ≤ rightArcPhase S y :=
    Real.arccos_le_arccos (sub_le_sub_left hc S)
  exact add_lt_add_of_lt_of_le hxy hg

theorem rightArcCoordinate_continuous (S : ℝ) : Continuous (rightArcCoordinate S) := by
  unfold rightArcCoordinate rightArcPhase
  fun_prop

theorem rightArcCoordinate_at_branch (S : ℝ) (hS : 0 < S ∧ S < 2) :
    rightArcCoordinate S (-rightBranchEndpoint S) = -rightBranchEndpoint S := by
  unfold rightArcCoordinate rightArcPhase
  rw [Real.cos_neg, rightBranchEndpoint_cos S hS]
  simp

theorem rightArcCoordinate_at_zero (S : ℝ) :
    rightArcCoordinate S 0 = rightBranchEndpoint S := by
  simp [rightArcCoordinate, rightArcPhase, rightBranchEndpoint]

/-- Exact image of the physical right-arc coordinate; both branch and
zero-angle endpoints are retained. -/
theorem rightArcCoordinate_image (S : ℝ) (hS : 0 < S ∧ S < 2) :
    rightArcCoordinate S '' Icc (-rightBranchEndpoint S) 0 =
      Icc (-rightBranchEndpoint S) (rightBranchEndpoint S) := by
  have hm : MonotoneOn (rightArcCoordinate S) (Icc (-rightBranchEndpoint S) 0) := by
    apply (rightArcCoordinate_strictMonoOn S).monotoneOn.mono
    intro w hw
    have hb : rightBranchEndpoint S ≤ Real.pi := Real.arccos_le_pi (S - 1)
    exact ⟨by linarith [hw.1], hw.2⟩
  have h := (rightArcCoordinate_continuous S).continuousOn.image_Icc_of_monotoneOn
    (by linarith [rightBranchEndpoint_pos S hS.2]) hm
  simpa only [rightArcCoordinate_at_branch S hS, rightArcCoordinate_at_zero] using h

theorem rightArcCoordinate_inside_discriminant_interval
    (S w : ℝ) (hS : 0 < S ∧ S < 2)
    (hw : w ∈ Icc (-rightBranchEndpoint S) 0) :
    rightArcCoordinate S w ∈ Ioo (-2 * Real.arccos (S / 2))
      (2 * Real.arccos (S / 2)) := by
  have hv : rightArcCoordinate S w ∈
      Icc (-rightBranchEndpoint S) (rightBranchEndpoint S) := by
    rw [← rightArcCoordinate_image S hS]
    exact ⟨w, hw, rfl⟩
  have hb := rightBranchEndpoint_lt_two_angle S hS
  constructor <;> linarith [hv.1, hv.2]

/-- The correct unsquared inverse denominator is positive at every actual
right-arc point, including its lower branch endpoint. -/
theorem rightArc_inverse_denominator_pos
    (S w : ℝ) (hS : 0 < S ∧ S < 2)
    (hw : w ∈ Icc (-rightBranchEndpoint S) 0) :
    0 < Real.sin (rightArcPhase S w) - Real.sin w := by
  have hg := rightArcPhase_range S w hS.1
  have hn := Real.sin_nonneg_of_nonneg_of_le_pi hg.1 hg.2.le
  by_cases hw0 : w = 0
  · subst w
    have hp : 0 < rightArcPhase S 0 := by
      unfold rightArcPhase
      apply Real.arccos_pos.mpr
      simpa using (by linarith [hS.2] : S - 1 < 1)
    simpa using Real.sin_pos_of_pos_of_lt_pi hp hg.2
  · have hnw : Real.sin w < 0 :=
      Real.sin_neg_of_neg_of_neg_pi_lt (lt_of_le_of_ne hw.2 hw0)
        (by linarith [hw.1, rightBranchEndpoint_lt_pi S hS.1])
    linarith

/-- The local analytic inverse and its positive curvature are now obtained
at every point of the actual physical right arc with no denominator premise
left to supply. -/
theorem exists_joint_inverse_on_right_arc
    (S w : ℝ) (hS : 0 < S ∧ S < 2)
    (hw : w ∈ Icc (-rightBranchEndpoint S) 0) :
    ∃ (U : (ℂ × ℂ) → ℂ) (c : ℝ), 0 < c ∧
      AnalyticAt ℂ U ((S : ℂ), (rightArcCoordinate S w : ℂ)) ∧
      U ((S : ℂ), (rightArcCoordinate S w : ℂ)) = w ∧
      ∀ᶠ q in 𝓝 ((S : ℂ), (rightArcCoordinate S w : ℂ)),
        Complex.cos (U q) + Complex.cos (q.2 - U q) = q.1 ∧
        HasDerivAt (deriv (fun z => U (q.1, z)))
          (inverseCurvature q.1 (U q) (q.2 - U q)) q.2 ∧
        c ≤ (inverseCurvature q.1 (U q) (q.2 - U q)).re := by
  have hsum : Real.cos w + Real.cos (rightArcPhase S w) = S := by
    rw [rightArcPhase_cos S w hS hw]
    ring
  have h := exists_joint_inverse_positive_curvature w (rightArcPhase S w)
    (by simpa only [hsum] using hS.1) (rightArc_inverse_denominator_pos S w hS hw)
  simpa only [← Complex.ofReal_cos, ← Complex.ofReal_add, hsum,
    rightArcCoordinate] using h

end IsingBulk.AnisoF002.Isotropic
