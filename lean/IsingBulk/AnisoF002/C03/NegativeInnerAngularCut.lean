import IsingBulk.AnisoF002.C03.NegativeActualAllAnglePole
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# A complete fixed real-torus cutoff for inner pole extraction

The unsigned shortest angle is continuous on the entire real circle and
has exactly the original cosine.  It is used only to select the same
phase pole; the physical numerator is evaluated at the original angles.
Thus no sign information or angular sector is removed from the density.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter
open scoped Topology BigOperators

def unsignedShortAngle (q : ℝ) : ℝ := Real.arccos (Real.cos q)

def angularShortSquare {n : ℕ} (q : Fin n → ℝ) : ℝ :=
  ∑ i, unsignedShortAngle (q i) ^ 2

def complexUnsignedAngles {n : ℕ} (q : Fin n → ℝ) : Fin n → ℂ :=
  fun i => (unsignedShortAngle (q i) : ℂ)

theorem unsignedShortAngle_nonneg (q : ℝ) : 0 ≤ unsignedShortAngle q := Real.arccos_nonneg _

theorem unsignedShortAngle_le_pi (q : ℝ) : unsignedShortAngle q ≤ Real.pi := Real.arccos_le_pi _

theorem unsignedShortAngle_cos (q : ℝ) : Real.cos (unsignedShortAngle q) = Real.cos q :=
  Real.cos_arccos (Real.neg_one_le_cos q) (Real.cos_le_one q)

theorem unsignedShortAngle_continuous : Continuous unsignedShortAngle :=
  Real.continuous_arccos.comp Real.continuous_cos

theorem angularShortSquare_continuous (n : ℕ) : Continuous (angularShortSquare (n := n)) :=
  continuous_finsetSum _ (fun i _ => (unsignedShortAngle_continuous.comp (continuous_apply i)).pow 2)

theorem complexUnsignedAngles_continuous (n : ℕ) : Continuous (complexUnsignedAngles (n := n)) :=
  continuous_pi fun i => Complex.continuous_ofReal.comp
    (unsignedShortAngle_continuous.comp (continuous_apply i))

theorem unsignedShortAngle_quadratic_lower (q : ℝ) :
    2 / Real.pi ^ 2 * unsignedShortAngle q ^ 2 ≤ 1 - Real.cos q := by
  have he := Real.cos_le_one_sub_mul_cos_sq (x := unsignedShortAngle q)
    (by rw [abs_of_nonneg (unsignedShortAngle_nonneg q)]; exact unsignedShortAngle_le_pi q)
  rw [unsignedShortAngle_cos] at he
  linarith

theorem angularShortSquare_cosine_lower {n : ℕ} (q : Fin n → ℝ) :
    2 / Real.pi ^ 2 * angularShortSquare q ≤ ∑ i, (1 - Real.cos (q i)) := by
  simpa only [angularShortSquare, Finset.mul_sum] using
    Finset.sum_le_sum (s := Finset.univ) (fun i _ => unsignedShortAngle_quadratic_lower (q i))

theorem complexUnsignedAngles_displacement {n : ℕ} (q : Fin n → ℝ) :
    displacementSquare n (complexUnsignedAngles q) = angularShortSquare q := by
  unfold displacementSquare complexUnsignedAngles angularShortSquare
  apply Finset.sum_congr rfl
  intro i _
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem complexUnsignedAngles_mem_ball {n : ℕ} {q : Fin n → ℝ} {σ : ℝ}
    (hσ : 0 < σ) (hQ : angularShortSquare q < σ ^ 2) :
    complexUnsignedAngles q ∈ Metric.ball 0 σ := by
  rw [Metric.mem_ball, dist_zero_right, pi_norm_lt_iff hσ]
  intro i
  have hi : unsignedShortAngle (q i) ^ 2 ≤ angularShortSquare q :=
    Finset.single_le_sum (fun j _ => sq_nonneg (unsignedShortAngle (q j))) (Finset.mem_univ i)
  rw [complexUnsignedAngles, Complex.norm_real, Real.norm_of_nonneg (unsignedShortAngle_nonneg _)]
  nlinarith [unsignedShortAngle_nonneg (q i)]

theorem negativeGlobalPhase_unsigned (B : ℂ → ℂ) (φ : ℝ) (t : ℂ) (q : ℝ) :
    negativeGlobalPhase B φ (t, (unsignedShortAngle q : ℂ)) =
      negativeGlobalPhase B φ (t, (q : ℂ)) := by
  unfold negativeGlobalPhase localNegativeDispersion
  rw [← Complex.ofReal_cos, ← Complex.ofReal_cos, unsignedShortAngle_cos]

theorem centeredPhaseAverage_unsigned (B : ℂ → ℂ) (φ : ℝ) (n : ℕ)
    (q : Fin n → ℝ) (γ t : ℂ) :
    centeredPhaseAverage n (negativeGlobalPhase B φ) γ 0 (complexUnsignedAngles q) t =
      centeredPhaseAverage n (negativeGlobalPhase B φ) γ 0 (fun i => (q i : ℂ)) t := by
  unfold centeredPhaseAverage
  simp only [zero_add, complexUnsignedAngles, negativeGlobalPhase_unsigned]

end
end IsingBulk.AnisoF002.NegativeHT
