import IsingBulk.Anisotropic.RegularEdges.AngularWrapping
import IsingBulk.First.PeriodicLiftIntegral

namespace IsingBulk.Anisotropic.RegularEdges
noncomputable section
open IsingBulk.First IsingBulk.HT.Contour Set MeasureTheory
open scoped BigOperators

theorem wrapAngle_add_period (q : ℝ) : wrapAngle (q+2*Real.pi)=wrapAngle q := by
  simp [wrapAngle,Real.Angle.coe_add,Real.Angle.coe_two_pi]

theorem wrappedDependentAngles_update (n : ℕ) (q : Fin n → ℝ) (i : Fin n) (j : Fin (n+1)) :
    wrapAngle (physicalDependentAngles n (Function.update q i (q i+2*Real.pi)) j)=
      wrapAngle (physicalDependentAngles n q j) := by
  have hs : (∑ k, Function.update q i (q i+2*Real.pi) k)=(∑ k,q k)+2*Real.pi := by
    rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
    rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ i) q]
    ring
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simp only [physicalDependentAngles,Fin.snoc_last,hs]
    simp [wrapAngle,Real.Angle.coe_add,Real.Angle.coe_neg,Real.Angle.coe_two_pi]
  · simp only [physicalDependentAngles,Fin.snoc_castSucc]
    by_cases hk : k=i
    · subst k
      simp only [Function.update_self,wrapAngle_add_period]
    · rw [Function.update_of_ne hk]

theorem complexAngularDensity_dependent_periodic (n : ℕ) (lam : ℝ) (z : ℂ) :
    CoordinatePeriodic n (fun q => complexAngularDensity lam z
      (fun i => (physicalDependentAngles n q i:ℂ))) := by
  intro q i
  dsimp only
  rw [← complexAngularDensity_wrapAngle lam z
    (physicalDependentAngles n (Function.update q i (q i+2*Real.pi))),
    ← complexAngularDensity_wrapAngle lam z (physicalDependentAngles n q)]
  congr 1
  funext j
  rw [wrappedDependentAngles_update]

theorem angleBox_integral_eq_centered (n : ℕ) (f : (Fin n → ℝ) → ℂ)
    (hf : Continuous f) (hp : CoordinatePeriodic n f) :
    (∫ q in angleBox n, f q)=∫ q in Icc (fun _ => -Real.pi) (fun _ => Real.pi), f q := by
  let c : Fin n → ℝ := fun _ => -Real.pi
  let K : Set (Fin n → ℝ) := Icc (fun _ => -Real.pi) (fun _ => Real.pi)
  have hm (q : Fin n → ℝ) : q+c∈K ↔ q∈angleBox n := by
    constructor <;> intro h <;> constructor <;> intro i
    · have hh := h.1 i
      change -Real.pi≤q i+-Real.pi at hh
      linarith
    · have hh := h.2 i
      change q i+-Real.pi≤Real.pi at hh
      linarith
    · have hh := h.1 i
      change -Real.pi≤q i+-Real.pi
      linarith
    · have hh := h.2 i
      change q i+-Real.pi≤Real.pi
      linarith
  have he : (fun q => K.indicator f (q+c))=
      (angleBox n).indicator (fun q => f (q+c)) := by
    funext q
    by_cases hq : q∈angleBox n
    · simp only [indicator_of_mem hq,indicator_of_mem ((hm q).mpr hq)]
    · simp only [indicator_of_notMem hq,indicator_of_notMem (not_congr (hm q) |>.mpr hq)]
  have ht := integral_add_right_eq_self (μ := volume) (K.indicator f) c
  rw [he] at ht
  rw [integral_indicator (show MeasurableSet (angleBox n) from measurableSet_Icc),
    integral_indicator (show MeasurableSet K from measurableSet_Icc)] at ht
  exact (angleBox_integral_shift n f hf hp c).symm.trans ht

theorem complexAngularDensity_dependent_continuous (n : ℕ) {lam : ℝ} {z : ℂ}
    (hz : z∉spectralSet lam) (hS : spectralS z≠0) :
    Continuous (fun q : Fin n → ℝ => complexAngularDensity lam z
      (fun i => (physicalDependentAngles n q i:ℂ))) := by
  have hp : Continuous (fun q : Fin n → ℝ => fun i => (physicalDependentAngles n q i:ℂ)) :=
    continuous_pi (fun i => Complex.continuous_ofReal.comp
      ((continuous_apply i).comp (physicalDependentAngles_continuous n)))
  apply continuous_iff_continuousAt.mpr
  intro q
  exact (complexAngularDensity_joint_analyticAt (by omega) hz hS
    (physicalDependentAngles n q)).continuousAt.comp
      (f := fun q => (z,fun i => (physicalDependentAngles n q i:ℂ)))
      (continuous_const.prodMk hp).continuousAt

theorem unscaledAngularCoefficient_eq_centered (n : ℕ) {lam : ℝ} {z : ℂ}
    (hz : z∉spectralSet lam) (hS : spectralS z≠0) :
    unscaledAngularCoefficient n lam z =
      ((n+1).factorial:ℂ)⁻¹*((2*(Real.pi:ℂ))⁻¹)^n *
        ∫ q in Icc (fun _ : Fin n => -Real.pi) (fun _ => Real.pi),
          complexAngularDensity lam z (fun i => (physicalDependentAngles n q i:ℂ)) := by
  unfold unscaledAngularCoefficient
  rw [multiAngleIntegral_eq_box n _ (complexAngularDensity_dependent_continuous n hz hS),
    angleBox_integral_eq_centered n _ (complexAngularDensity_dependent_continuous n hz hS)
      (complexAngularDensity_dependent_periodic n lam z)]

end
end IsingBulk.Anisotropic.RegularEdges
