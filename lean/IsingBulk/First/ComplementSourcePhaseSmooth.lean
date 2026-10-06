import IsingBulk.First.ComplementSourceSmooth
import IsingBulk.First.ComplementPhaseSum

/-! Joint smoothness of the complete actual normalized auxiliary phase. -/
namespace IsingBulk.First
noncomputable section
open scoped BigOperators ContDiff
attribute [local fun_prop] source_complexOfReal_contDiff

/-- The exponent is the literal denominator with its proved complex prefactor. -/
theorem sourceAngularExponent_eq_denominator {N : ℕ} (r : ℝ) (s : ℂ)
    (f : SingularFactorIndex N) (hf : validSourceFactor f) (u : DoubleAngularVector N) :
    sourceAngularExponent r s (fun _ => 1) (fun _ => 1) f u =
      -sourceFactorExponentialScalar f *
        sourceFactorDenominator s (angleTuple r u.1) (angleTuple r u.2) f := by
  rcases f with b | (⟨b,i,j⟩ | i)
  · cases b <;> simp [sourceAngularExponent, singularFactorExponent, sourceFactorExponentialScalar,
      sourceFactorDenominator, coordinateProduct, angleTuple, anglePoint_eq_angularCurve]
  · change i < j at hf
    cases b <;> simp [sourceAngularExponent, singularFactorExponent, sourceFactorExponentialScalar,
      sourceFactorDenominator, hf, angleTuple, anglePoint_eq_angularCurve]
  · simp [sourceAngularExponent, singularFactorExponent, sourceFactorExponentialScalar,
      sourceFactorDenominator, angleTuple, anglePoint_eq_angularCurve]

/-- The actual phase is jointly C∞ in radius, temperature, normalized
auxiliary coordinates, and real angles. -/
theorem sourcePhaseSum_joint_contDiffAt {N : ℕ} {ι : Type*} [Fintype ι]
    (J : ι → SingularFactorIndex N) (hJ : ∀ i, validSourceFactor (J i))
    (r : ℝ) (s : ℂ) (η : ι → ℝ) (u : DoubleAngularVector N) (hr : r ≠ 0) (hs : s ≠ 0) :
    ContDiffAt ℝ ∞ (fun q : ((ℝ × ℂ) × (ι → ℝ)) × DoubleAngularVector N =>
      sourcePhaseSum q.1.1.1 q.1.1.2 (fun _ => 1) (fun _ => 1) J q.1.2 q.2) (((r,s),η),u) := by
  have hx (i) : ContDiffAt ℝ ∞
      (fun q : ((ℝ × ℂ) × (ι → ℝ)) × DoubleAngularVector N => angleTuple q.1.1.1 q.2.1 i)
      (((r,s),η),u) :=
    anglePoint_joint_contDiff.contDiffAt.comp (((r,s),η),u)
      (show ContDiffAt ℝ ∞ (fun q : ((ℝ × ℂ) × (ι → ℝ)) × DoubleAngularVector N =>
        (q.1.1.1,q.2.1 i)) (((r,s),η),u) by fun_prop)
  have hy (i) : ContDiffAt ℝ ∞
      (fun q : ((ℝ × ℂ) × (ι → ℝ)) × DoubleAngularVector N => angleTuple q.1.1.1 q.2.2 i)
      (((r,s),η),u) :=
    anglePoint_joint_contDiff.contDiffAt.comp (((r,s),η),u)
      (show ContDiffAt ℝ ∞ (fun q : ((ℝ × ℂ) × (ι → ℝ)) × DoubleAngularVector N =>
        (q.1.1.1,q.2.2 i)) (((r,s),η),u) by fun_prop)
  unfold sourcePhaseSum
  apply ContDiffAt.sum
  intro i _
  simp_rw [sourceAngularExponent_eq_denominator _ _ (J i) (hJ i)]
  have hd := sourceFactorDenominator_contDiffAt hx hy
    (show ContDiffAt ℝ ∞ (fun q : ((ℝ × ℂ) × (ι → ℝ)) × DoubleAngularVector N =>
      q.1.1.2) (((r,s),η),u) by fun_prop)
    (fun _ => anglePoint_ne_zero_of_radius hr _) (fun _ => anglePoint_ne_zero_of_radius hr _) hs (J i)
  exact (show ContDiffAt ℝ ∞ (fun q : ((ℝ × ℂ) × (ι → ℝ)) × DoubleAngularVector N =>
    (q.1.2 i : ℂ)) (((r,s),η),u) by fun_prop).mul (contDiffAt_const.mul hd)

end
end IsingBulk.First
