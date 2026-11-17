import IsingBulk.AnisoF002.C03.NegativeActualPoleDensityGeometry
import IsingBulk.AnisoF002.C03.RegularPhaseDifferential
import IsingBulk.AnisoF002.C03.RegularEdgeGaussian

/-!
# One actual negative-edge phase on the whole angular circle

The generic checked regular-edge root control is applied with
c(t)=cos(phi)+B(t)t and a(t)=-B(t).  The complex phase is the principal
logarithm of that same explicit root.  Its center, parity and unsquared
dispersion identities hold exactly; its common disk controls every real
angle before the particle number is selected.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter IsingBulk.AnisoF002.RegularTail IsingBulk.AnisoF002.RegularTail.C03
open scoped Topology BigOperators

def negativeGlobalCenter (B : ℂ → ℂ) (φ : ℝ) (t : ℂ) : ℂ :=
  (Real.cos φ : ℂ) + B t * t

def negativeGlobalCoefficient (B : ℂ → ℂ) (t : ℂ) : ℂ := -B t

def negativeGlobalPhase (B : ℂ → ℂ) (φ : ℝ) (p : ℂ × ℂ) : ℂ :=
  upperEdgePhase (localNegativeDispersion B φ p)

theorem negativeGlobalCenter_analyticAt {B : ℂ → ℂ} {φ : ℝ} (hB : AnalyticAt ℂ B 0) :
    AnalyticAt ℂ (negativeGlobalCenter B φ) 0 := analyticAt_const.add (hB.mul analyticAt_id)

theorem negativeGlobalPhase_as_edge (B : ℂ → ℂ) (φ : ℝ) (p : ℂ × ℂ) :
    negativeGlobalPhase B φ p =
      edgeJointPhase (negativeGlobalCenter B φ) (negativeGlobalCoefficient B) (p.1, Complex.cos p.2) := by
  unfold negativeGlobalPhase edgeJointPhase localNegativeDispersion
    negativeGlobalCenter negativeGlobalCoefficient
  congr 1
  ring

theorem negativeGlobalPhase_real (B : ℂ → ℂ) (φ : ℝ) (t : ℂ) (q : ℝ) :
    negativeGlobalPhase B φ (t, (q : ℂ)) =
      edgeAnglePhase (negativeGlobalCenter B φ) (negativeGlobalCoefficient B) t q := by
  rw [negativeGlobalPhase_as_edge]
  simp only [edgeAnglePhase, Complex.ofReal_cos]

theorem negativeGlobalPhase_cosh (B : ℂ → ℂ) (φ : ℝ) (p : ℂ × ℂ) :
    Complex.cosh (negativeGlobalPhase B φ p) = localNegativeDispersion B φ p :=
  upperEdgePhase_cosh _

theorem negativeGlobalPhase_even (B : ℂ → ℂ) (φ : ℝ) (t d : ℂ) :
    negativeGlobalPhase B φ (t, -d) = negativeGlobalPhase B φ (t, d) := by
  simp [negativeGlobalPhase, localNegativeDispersion, Complex.cos_neg]

theorem negativeGlobalPhase_center (B : ℂ → ℂ) {φ : ℝ}
    (hφ : 0 < φ) (hπ : φ < Real.pi) (d : ℂ) :
    negativeGlobalPhase B φ (1 - Complex.cos d, d) = (φ : ℂ) * Complex.I := by
  simpa [negativeGlobalPhase, localNegativeDispersion] using upperEdgePhase_cos hφ hπ

theorem negativeGlobalPhase_analyticAt_zero {B : ℂ → ℂ} {φ : ℝ}
    (hB : AnalyticAt ℂ B 0) (hφ : 0 < φ) (hπ : φ < Real.pi) :
    AnalyticAt ℂ (negativeGlobalPhase B φ) (0, 0) := by
  have hb : |Real.cos φ| < 1 :=
    abs_cos_lt_one_of_sin_ne_zero
      (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hφ hπ))
  have hW := edge_discriminant_slit (Or.inr
    ⟨show (Real.cos φ : ℂ).im = 0 by simp, by simpa only [Complex.ofReal_re] using hb⟩)
  exact (upperEdgePhase_analyticAt hW).comp_of_eq
    (localNegativeDispersion_analyticAt (φ := φ) hB) (by simp [localNegativeDispersion])

theorem exists_negative_global_controls {B : ℂ → ℂ} {φ : ℝ}
    (hB : AnalyticAt ℂ B 0) (hφ : 0 < φ) (hπ : φ < Real.pi) (hBi : (B 0).im < 0) :
    Nonempty (RegularEdgeControl (negativeGlobalCenter B φ) (negativeGlobalCoefficient B)) ∧
    Nonempty (RegularEdgePhaseControl (negativeGlobalCenter B φ) (negativeGlobalCoefficient B)) := by
  have hb : |Real.cos φ| < 1 :=
    abs_cos_lt_one_of_sin_ne_zero
      (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hφ hπ))
  have hc := negativeGlobalCenter_analyticAt (φ := φ) hB
  have ha : AnalyticAt ℂ (negativeGlobalCoefficient B) 0 := hB.neg
  have hc0 : negativeGlobalCenter B φ 0 = (Real.cos φ : ℂ) := by simp [negativeGlobalCenter]
  have ha0 : 0 < (negativeGlobalCoefficient B 0).im := by
    simpa only [negativeGlobalCoefficient, Complex.neg_im] using neg_pos.mpr hBi
  exact ⟨exists_regular_edge_control hc ha hc0 hb ha0,
    exists_regular_edge_phase_control hc ha hc0 hb ha0⟩

end
end IsingBulk.AnisoF002.NegativeHT
