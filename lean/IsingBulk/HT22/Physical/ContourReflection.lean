import IsingBulk.HT22.Physical.WholeDeformation
import IsingBulk.Preferred22.ContourPartition

namespace IsingBulk.HT22.Physical
noncomputable section
open Set MeasureTheory IsingBulk.Preferred22 IsingBulk.Tail
open scoped BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false

theorem canceledPair_inverse (a b z w : ℂ) (ha : a≠0) (hb : b≠0) :
    canceledPair a⁻¹ b⁻¹ z w = canceledPair a b z w := by
  unfold canceledPair
  by_cases hz : 1-z*w=0
  · simp [hz]
  · field_simp
    ring

theorem complexSignedDensity_reflect (negative : Bool) {N : ℕ} (t : ℂ)
    (w : Fin N → ℂ) :
    complexSignedDensity negative (t,-w) = complexSignedDensity negative (t,w) := by
  have hy (i) : complexAngle (-w i)=(complexAngle (w i))⁻¹ := by
    simp [complexAngle, mul_neg, Complex.exp_neg]
  simp only [complexSignedDensity,complexRoot,Pi.neg_apply,Complex.cos_neg]
  simp_rw [hy]
  congr 1
  unfold canceledPairProduct
  apply Finset.prod_congr rfl
  intro i _
  apply Finset.prod_congr rfl
  intro j _
  exact canceledPair_inverse _ _ _ _ (Complex.exp_ne_zero _) (Complex.exp_ne_zero _)

theorem bareContourDensity_reflect (negative : Bool) {N : ℕ} (τ : ℝ) (p : ℝ → ℝ)
    (t : ℂ) (θ : Fin N → ℝ) :
    bareContourDensity negative τ p (fun x => p (-x)) t (-θ) =
      bareContourDensity negative τ p (fun x => p (-x)) t θ := by
  unfold bareContourDensity
  rw [preferred_contourMatrix_reflect,preferred_deformedAngles_reflect,
    complexSignedDensity_reflect]

theorem periodic_deriv {p : ℝ → ℝ} {a : ℝ} (hp : Function.Periodic p a) :
    Function.Periodic (deriv p) a := by
  intro x
  have he : (fun y => p (y+a))=p := funext hp
  have hd := congrArg (fun f : ℝ → ℝ => deriv f x) he
  simpa only [deriv_comp_add_const] using hd

/-- Equality of the complete coupled density from its literal periodic data.
No independent-coordinate product approximation is used. -/
theorem bareContourDensity_congr_data (negative : Bool) {N : ℕ}
    (τ : ℝ) (p m : ℝ → ℝ) (t : ℂ) (θ ψ : Fin N → ℝ)
    (hy : ∀ i, angleRoot (θ i)=angleRoot (ψ i))
    (hp : ∀ i,p (θ i)=p (ψ i)) (hm : ∀ i,m (θ i)=m (ψ i))
    (hdp : ∀ i,deriv p (θ i)=deriv p (ψ i))
    (hdm : ∀ i,deriv m (θ i)=deriv m (ψ i)) :
    bareContourDensity negative τ p m t θ = bareContourDensity negative τ p m t ψ := by
  have hs : balancedShift τ p m θ=balancedShift τ p m ψ := by
    ext i
    simp only [balancedShift,Preferred22.occupancy,hp,hm]
  have hM : preferredContourMatrix τ p m θ=preferredContourMatrix τ p m ψ := by
    ext i j
    simp only [preferredContourMatrix,hp,hm,hdp,hdm]
  have he : (fun i => Complex.exp (Complex.I*deformedAngles τ p m θ i)) =
      fun i => Complex.exp (Complex.I*deformedAngles τ p m ψ i) := by
    funext i
    have hθ : Complex.I*deformedAngles τ p m θ i =
        Complex.I*(θ i:ℂ)+(balancedShift τ p m θ i:ℂ) := by
      simp only [deformedAngles,mul_sub,← mul_assoc,Complex.I_mul_I]
      ring
    have hψ : Complex.I*deformedAngles τ p m ψ i =
        Complex.I*(ψ i:ℂ)+(balancedShift τ p m ψ i:ℂ) := by
      simp only [deformedAngles,mul_sub,← mul_assoc,Complex.I_mul_I]
      ring
    rw [hθ,hψ,Complex.exp_add,Complex.exp_add,hs]
    exact congrArg (fun z => z*Complex.exp (balancedShift τ p m ψ i:ℂ)) (hy i)
  unfold bareContourDensity
  rw [hM,← rootFreeSignedDensity_eq_complexSignedDensity,
    ← rootFreeSignedDensity_eq_complexSignedDensity,he]

/-- The signed affine reflection differs from ordinary negation only by a
full period in its dependent angle. -/
theorem signed_reflection_periodic_data {n : ℕ} (negative : Bool) (q : Fin n → ℝ)
    (f : ℝ → ℝ) (hf : Function.Periodic f (2*Real.pi)) (i : Fin (n+1)) :
    f (constrainedAngles negative n (-q) i)=f (-constrainedAngles negative n q i) := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [constrainedAngles, Fin.snoc_last, Pi.neg_apply, Finset.sum_neg_distrib,sub_neg_eq_add]
    cases negative
    · simp [constraintAngle]
    · simp only [constraintAngle, ↓reduceIte]
      rw [show Real.pi+∑ j,q j = -(Real.pi-∑ j,q j)+2*Real.pi by ring]
      exact hf _
  · simp only [constrainedAngles,Fin.snoc_castSucc,Pi.neg_apply]

theorem bareContourDensity_constrained_reflect (negative : Bool) (n : ℕ)
    (τ : ℝ) (p : ℝ → ℝ) (hpp : Function.Periodic p (2*Real.pi))
    (t : ℂ) (q : Fin n → ℝ) :
    bareContourDensity negative τ p (fun x => p (-x)) t (constrainedAngles negative n (-q)) =
      bareContourDensity negative τ p (fun x => p (-x)) t (constrainedAngles negative n q) := by
  let m := fun x => p (-x)
  have hmp : Function.Periodic m (2*Real.pi) := by
    intro x
    change p (-(x+2*Real.pi))=p (-x)
    rw [neg_add,show -x+- (2*Real.pi)= -x-2*Real.pi by ring]
    exact hpp.sub_eq _
  calc
    _ = bareContourDensity negative τ p m t (-(constrainedAngles negative n q)) := by
      apply bareContourDensity_congr_data
      · intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp only [constrainedAngles, Fin.snoc_last, Pi.neg_apply,Finset.sum_neg_distrib,sub_neg_eq_add]
          cases negative
          · simp [constraintAngle]
          · simp only [constraintAngle, ↓reduceIte]
            rw [show Real.pi+∑ j,q j = -(Real.pi-∑ j,q j)+2*Real.pi by ring]
            exact angleRoot_periodic _
        · simp only [constrainedAngles,Fin.snoc_castSucc,Pi.neg_apply]
      · exact signed_reflection_periodic_data negative q p hpp
      · exact signed_reflection_periodic_data negative q m hmp
      · exact signed_reflection_periodic_data negative q (deriv p) (periodic_deriv hpp)
      · exact signed_reflection_periodic_data negative q (deriv m) (periodic_deriv hmp)
    _ = _ := bareContourDensity_reflect negative τ p t _

end
end IsingBulk.HT22.Physical
