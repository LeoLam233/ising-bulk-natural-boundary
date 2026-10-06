import IsingBulk.Tail.CompactDiameterIntegral

namespace IsingBulk.Tail
noncomputable section
open Set MeasureTheory
open scoped BigOperators

theorem compact_diameter_dominated_integral {N : ℕ} {R A B : ℝ}
    (K : (Fin N → ℝ) → ℝ) (hK0 : ∀ x, 0 ≤ K x)
    (hK : IntegrableOn (fun x => allBranchExteriorDiameter x*K x)
      (Icc (fun _ => -R) (fun _ => R)))
    (hBudget : (∫ x in Icc (fun _ => -R) (fun _ => R), allBranchExteriorDiameter x*K x) ≤ B)
    {S : Set (Fin N → ℝ)} (hS : MeasurableSet S)
    (hSub : S ⊆ Icc (fun _ => -R) (fun _ => R))
    (F : (Fin N → ℝ) → ℂ) (hF : IntegrableOn F S) (hA : 0 ≤ A)
    (hPoint : ∀ x ∈ S, ‖F x‖ ≤ A*(allBranchExteriorDiameter x*K x)) :
    (∫ x in S, ‖F x‖) ≤ A*B := by
  have hInt := hK.mono_set hSub
  calc
    _ ≤ ∫ x in S, A*(allBranchExteriorDiameter x*K x) :=
      setIntegral_mono_on hF.norm (hInt.const_mul A) hS hPoint
    _ = A*(∫ x in S, allBranchExteriorDiameter x*K x) := integral_const_mul _ _
    _ ≤ A*(∫ x in Icc (fun _ => -R) (fun _ => R), allBranchExteriorDiameter x*K x) :=
      mul_le_mul_of_nonneg_left (setIntegral_mono_set hK
        (Filter.Eventually.of_forall (fun x => mul_nonneg (allBranchExterior_diameter_nonneg x) (hK0 x)))
        (Filter.Eventually.of_forall hSub)) hA
    _ ≤ _ := mul_le_mul_of_nonneg_left hBudget hA

/-- Near full collision, the coarea loss is exactly one diameter power.
The remaining power can be arbitrarily large and depend on N. -/
theorem compact_near_diameter_integral {N : ℕ} {R A B ρ : ℝ} (hρ : 0 ≤ ρ)
    (P : ℕ) (K : (Fin N → ℝ) → ℝ) (hK0 : ∀ x, 0 ≤ K x)
    (hK : IntegrableOn (fun x => allBranchExteriorDiameter x*K x)
      (Icc (fun _ => -R) (fun _ => R)))
    (hBudget : (∫ x in Icc (fun _ => -R) (fun _ => R), allBranchExteriorDiameter x*K x) ≤ B)
    {S : Set (Fin N → ℝ)} (hS : MeasurableSet S)
    (hSub : S ⊆ Icc (fun _ => -R) (fun _ => R))
    (hNear : ∀ x ∈ S, allBranchExteriorDiameter x ≤ ρ)
    (F : (Fin N → ℝ) → ℂ) (hF : IntegrableOn F S) (hA : 0 ≤ A)
    (hPoint : ∀ x ∈ S, ‖F x‖ ≤ A*allBranchExteriorDiameter x^(P+1)*K x) :
    (∫ x in S, ‖F x‖) ≤ (A*ρ^P)*B := by
  apply compact_diameter_dominated_integral K hK0 hK hBudget hS hSub F hF (by positivity)
  intro x hx
  apply (hPoint x hx).trans
  have hp := pow_le_pow_left₀ (allBranchExterior_diameter_nonneg x) (hNear x hx) P
  calc
    _ = (A*allBranchExteriorDiameter x^P)*(allBranchExteriorDiameter x*K x) := by rw [pow_succ]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hA)
      (mul_nonneg (allBranchExterior_diameter_nonneg x) (hK0 x))

/-- The separated region pays a single inverse diameter, independent of
the number of parameter derivatives in its numerator estimate. -/
theorem compact_far_diameter_integral {N : ℕ} {R A B ρ : ℝ} (hρ : 0 < ρ)
    (K : (Fin N → ℝ) → ℝ) (hK0 : ∀ x, 0 ≤ K x)
    (hK : IntegrableOn (fun x => allBranchExteriorDiameter x*K x)
      (Icc (fun _ => -R) (fun _ => R)))
    (hBudget : (∫ x in Icc (fun _ => -R) (fun _ => R), allBranchExteriorDiameter x*K x) ≤ B)
    {S : Set (Fin N → ℝ)} (hS : MeasurableSet S)
    (hSub : S ⊆ Icc (fun _ => -R) (fun _ => R))
    (hFar : ∀ x ∈ S, ρ ≤ allBranchExteriorDiameter x)
    (F : (Fin N → ℝ) → ℂ) (hF : IntegrableOn F S) (hA : 0 ≤ A)
    (hPoint : ∀ x ∈ S, ‖F x‖ ≤ A*K x) :
    (∫ x in S, ‖F x‖) ≤ (A/ρ)*B := by
  apply compact_diameter_dominated_integral K hK0 hK hBudget hS hSub F hF (div_nonneg hA hρ.le)
  intro x hx
  apply (hPoint x hx).trans
  calc
    A*K x = (A/ρ)*(ρ*K x) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hFar x hx) (hK0 x))
      (div_nonneg hA hρ.le)

end
end IsingBulk.Tail
