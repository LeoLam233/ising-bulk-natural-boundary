import IsingBulk.First.DoublePeriodicIntegral
import IsingBulk.First.FormFactorAnalytic

/-! Exact periodicity of the literal source angular densities, including every
remaining normalized Jacobian. -/
namespace IsingBulk.First
noncomputable section
open Set MeasureTheory
open scoped BigOperators

theorem anglePoint_add_period (r u : ℝ) : anglePoint r (u+2*Real.pi)=anglePoint r u :=
  periodic_circleMap 0 r u

theorem angleTuple_update_period {N : ℕ} (r : ℝ) (x : Fin N → ℝ) (i : Fin N) :
    angleTuple r (Function.update x i (x i+2*Real.pi)) = angleTuple r x := by
  funext j
  by_cases hj : j=i
  · subst j
    simp only [angleTuple, Function.update_self, anglePoint_add_period]
  · simp only [angleTuple, Function.update_of_ne hj]

theorem angleProductJacobian_update_period {N : ℕ} (r : ℝ) (x : Fin N → ℝ) (i : Fin N) :
    angleProductJacobian r (Function.update x i (x i+2*Real.pi)) = angleProductJacobian r x := by
  apply Finset.prod_congr rfl
  intro j _
  have hh := congrFun (angleTuple_update_period r x i) j
  change anglePoint r (Function.update x i (x i+2*Real.pi) j)=anglePoint r (x j) at hh
  simp only [angleJacobian,hh]

def sourceReducedAngularDensity {N : ℕ} (r : ℝ) (s : ℂ) (x : Fin N → ℝ) : ℂ :=
  angleProductJacobian r x * reducedDensity (fun i => globalRoot s (anglePoint r (x i))) (angleTuple r x)

theorem sourceReducedAngularDensity_periodic (N : ℕ) (r : ℝ) (s : ℂ) :
    CoordinatePeriodic N (sourceReducedAngularDensity r s) := by
  intro x i
  have he : (fun j => globalRoot s (anglePoint r (Function.update x i (x i+2*Real.pi) j))) =
      (fun j => globalRoot s (anglePoint r (x j))) := by
    funext j
    exact congrArg (globalRoot s) (congrFun (angleTuple_update_period r x i) j)
  simp only [sourceReducedAngularDensity, angleProductJacobian_update_period,angleTuple_update_period,he]

theorem sourceReducedAngularDensity_continuous (N : ℕ) (hN : 0 < N) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) {s : ℂ} (hm : r⁻¹-r < (sourceS s).im) :
    Continuous (sourceReducedAngularDensity (N := N) r s) := by
  have h := globalRoot_admissible hr hr1 hm
  have hh := reducedDensity_continuous_angles N hN r s (globalRoot s)
    (fun θ => h.toTuple N _ (fun _ => anglePoint_norm hr.le _))
  exact (angleProductJacobian_continuous r).mul hh

theorem weightedReducedFormFactor_eq_box (N : ℕ) (hN : 0 < N) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) {s : ℂ} (hm : r⁻¹-r < (sourceS s).im)
    (w : (Fin N → ℝ) → ℝ) (hw : Continuous w) :
    weightedReducedFormFactor N r (globalRoot s) w =
      (N.factorial:ℂ)⁻¹ * ∫ x in angleBox N, (w x:ℂ)*sourceReducedAngularDensity r s x := by
  have hc : Continuous (fun x : Fin N → ℝ => (w x:ℂ)*sourceReducedAngularDensity r s x) :=
    (Complex.continuous_ofReal.comp hw).mul
    (sourceReducedAngularDensity_continuous N hN hr hr1 hm)
  unfold weightedReducedFormFactor
  have he : (fun x : Fin N → ℝ => (w x:ℂ)*angleProductJacobian r x*
      reducedDensity (fun i => globalRoot s (anglePoint r (x i))) (angleTuple r x)) =
      (fun x => (w x:ℂ)*sourceReducedAngularDensity r s x) := by
    funext x
    simp only [sourceReducedAngularDensity,mul_assoc]
  rw [he,multiAngleIntegral_eq_box N _ hc]

theorem doubleAngularDensityOf_periodic (N : ℕ) (r : ℝ) (s : ℂ) :
    DoubleCoordinatePeriodicSections N (doubleAngularDensityOf r (doubleDensity s)) := by
  constructor
  · intro y x i
    simp only [doubleAngularDensityOf,angleProductJacobian_update_period,angleTuple_update_period]
  · intro x y i
    simp only [doubleAngularDensityOf,angleProductJacobian_update_period,angleTuple_update_period]

end
end IsingBulk.First
