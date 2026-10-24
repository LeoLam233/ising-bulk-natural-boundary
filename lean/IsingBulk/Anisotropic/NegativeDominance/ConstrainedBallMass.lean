import IsingBulk.Anisotropic.NegativeDominance.VandermondeBallBound
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open IsingBulk.First MeasureTheory Set
open scoped BigOperators

/-- The actual constrained energy ball in the independent angular coordinates. -/
def constrainedEnergyBall (n : ℕ) : Set (Fin n → ℝ) :=
  {x | (∑ i : Fin (n+1),(shapeExtend x i)^2)≤1}

def constrainedBallMass (n : ℕ) : ℝ :=
  ∫ x in constrainedEnergyBall n, firstVandermonde (shapeExtend x)^2

theorem constrainedEnergyBall_subset_box (n : ℕ) :
    constrainedEnergyBall n⊆Icc (fun _ => (-1 : ℝ)) (fun _ => (1 : ℝ)) := by
  intro x hx
  have hi (i : Fin n) : (x i)^2≤1 := by
    have h := Finset.single_le_sum (fun k (_ : k∈Finset.univ) => sq_nonneg (shapeExtend x k))
      (Finset.mem_univ i.castSucc)
    have hh := h.trans hx
    simpa using hh
  constructor <;> intro i <;> nlinarith only [hi i]

theorem constrained_box_volume (n : ℕ) :
    volume.real (Icc (fun _ : Fin n => (-1 : ℝ)) (fun _ => (1 : ℝ)))=2^n := by
  rw [measureReal_def,Real.volume_Icc_pi_toReal (by intro i; norm_num)]
  norm_num

theorem constrainedEnergyBall_finite (n : ℕ) : volume (constrainedEnergyBall n)<⊤ :=
  (measure_mono (constrainedEnergyBall_subset_box n)).trans_lt isCompact_Icc.measure_lt_top

/-- Genuine ball-mass suppression, including the full independent-coordinate
Lebesgue volume. No beta convergence or fixed particle index is used. -/
theorem constrainedBallMass_bound {n : ℕ} (hn : 1≤n) :
    constrainedBallMass n≤2^n*(16/((n+1 : ℕ) : ℝ))^((n+1).choose 2) := by
  have hb := norm_setIntegral_le_of_norm_le_const (constrainedEnergyBall_finite n)
    (f := fun x : Fin n → ℝ => firstVandermonde (shapeExtend x)^2)
    (C := (16/((n+1 : ℕ) : ℝ))^((n+1).choose 2)) (by
      intro x hx
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact vandermonde_sq_energy_ball (by omega) (shapeExtend x) hx)
  have hm : volume.real (constrainedEnergyBall n)≤2^n := by
    simpa only [constrained_box_volume] using measureReal_mono (μ := volume) (constrainedEnergyBall_subset_box n) isCompact_Icc.measure_lt_top.ne
  calc
    constrainedBallMass n ≤ ‖constrainedBallMass n‖ := le_abs_self _
    _ ≤ (16/((n+1 : ℕ) : ℝ))^((n+1).choose 2)*volume.real (constrainedEnergyBall n) := hb
    _ ≤ (16/((n+1 : ℕ) : ℝ))^((n+1).choose 2)*2^n := by gcongr
    _ = _ := by ring

end
end IsingBulk.Anisotropic.NegativeDominance
