import IsingBulk.First.AngularCoordinateSplit

/-! Variable-radius genuine normalized product contours and one-coordinate Fubini. -/
namespace IsingBulk.First
noncomputable section
open Set MeasureTheory
open scoped BigOperators

def variableAngleTuple {N : ℕ} (R : Fin N → ℝ) (θ : Fin N → ℝ) : Fin N → ℂ :=
  fun i => anglePoint (R i) (θ i)

def variableAngleJacobian {N : ℕ} (R : Fin N → ℝ) (θ : Fin N → ℝ) : ℂ :=
  ∏ i, angleJacobian (R i) (θ i)

def variableCircleIntegral {N : ℕ} (R : Fin N → ℝ) (f : (Fin N → ℂ) → ℂ) : ℂ :=
  ∫ θ in angleBox N, variableAngleJacobian R θ * f (variableAngleTuple R θ)

theorem variableAngleTuple_continuous {N : ℕ} (R : Fin N → ℝ) : Continuous (variableAngleTuple R) := by
  unfold variableAngleTuple anglePoint
  fun_prop

theorem variableAngleJacobian_continuous {N : ℕ} (R : Fin N → ℝ) :
    Continuous (variableAngleJacobian R) := by
  unfold variableAngleJacobian angleJacobian anglePoint
  fun_prop

theorem variableCircleIntegral_const_radius (N : ℕ) (r : ℝ) (f : (Fin N → ℂ) → ℂ)
    (hf : Continuous (fun θ : Fin N → ℝ => angleProductJacobian r θ*f (angleTuple r θ))) :
    variableCircleIntegral (fun _ : Fin N => r) f = multiCircleIntegral r N f := by
  rw [multiCircleIntegral_eq_angle, multiAngleIntegral_eq_box N _ hf]
  rfl

theorem variableAngleTuple_insertNth {n : ℕ} (i : Fin (n+1)) (R : Fin (n+1) → ℝ)
    (u : ℝ) (θ : Fin n → ℝ) :
    variableAngleTuple R (i.insertNth u θ) =
      i.insertNth (anglePoint (R i) u) (variableAngleTuple (fun j => R (i.succAbove j)) θ) := by
  funext j
  by_cases hj : j=i
  · subst j
    simp [variableAngleTuple]
  · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
    simp [variableAngleTuple]

theorem variableAngleJacobian_insertNth {n : ℕ} (i : Fin (n+1)) (R : Fin (n+1) → ℝ)
    (u : ℝ) (θ : Fin n → ℝ) :
    variableAngleJacobian R (i.insertNth u θ) =
      angleJacobian (R i) u * variableAngleJacobian (fun j => R (i.succAbove j)) θ := by
  unfold variableAngleJacobian
  rw [i.prod_univ_succAbove]
  simp

/-- Chosen coordinate innermost, retaining all other normalizing Jacobians. -/
theorem variableCircleIntegral_succAbove {n : ℕ} (i : Fin (n+1)) (R : Fin (n+1) → ℝ)
    (f : (Fin (n+1) → ℂ) → ℂ)
    (hf : Continuous (fun θ => variableAngleJacobian R θ*f (variableAngleTuple R θ))) :
    variableCircleIntegral R f = ∫ θ in angleBox n,
      variableAngleJacobian (fun j => R (i.succAbove j)) θ *
        normalizedCircleIntegral (R i) (fun w =>
          f (i.insertNth w (variableAngleTuple (fun j => R (i.succAbove j)) θ))) := by
  unfold variableCircleIntegral
  rw [angleBox_integral_succAbove n i _ hf]
  apply setIntegral_congr_fun measurableSet_Icc
  intro θ _
  dsimp only
  rw [normalizedCircleIntegral_eq_angle, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro u _
  dsimp only
  rw [variableAngleTuple_insertNth, variableAngleJacobian_insertNth]
  ring

end
end IsingBulk.First
