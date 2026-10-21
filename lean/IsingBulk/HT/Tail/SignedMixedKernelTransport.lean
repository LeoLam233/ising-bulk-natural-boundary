import IsingBulk.HT.Tail.SignedMixedSmooth
import IsingBulk.Tail.CompactSelectedLieDensity
import IsingBulk.Tail.MixedSourceNormalization

namespace IsingBulk.HT.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Tail IsingBulk.Lie IsingBulk.HT.Contour Set Filter
open scoped Topology ContDiff BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The actual two simple poles are frozen by the source transport field.
Their nonvanishing is proved on the same separated source domain. -/
theorem signed_mixed_actual_kernel_frozen (σ : ℂ) (hσ : ‖σ‖ = 1) {n : ℕ} (J : Finset (Fin (n+1))) (j q : Fin (n+1))
    (f : SelectorFunctions) {r : ℝ} (hr : 0<r) (τ lam : ℝ) (s : ℂ) (θ : Fin (n+1) → ℝ)
    (hj : j∈J) (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m)
    (hplateau : ∀ i,i∈J ∨ i=q → deriv f.p (θ i)=0 ∧ deriv f.m (θ i)=0)
    (hΩ : (s,θ)∈mixedSeparatedDomain J j q f r τ lam)
    (hYgap : ∀ x : Fin (n+1) → ℝ, ‖coordinateProduct (deformedPoint f r τ lam x)‖ < 1) :
    transport (mixedContourVelocity J j q f r τ lam) (signedMixedSimpleKernel σ f r τ lam) s θ=0 := by
  let Y := fun (_ : ℂ) (x : Fin (n+1) → ℝ) => coordinateProduct (deformedPoint f r τ lam x)
  let Z := fun (z : ℂ) (x : Fin (n+1) → ℝ) => coordinateProduct (fun i => globalRoot z (deformedPoint f r τ lam x i))
  have hY := mixedSeparated_Y_smooth J j q f r τ lam hp hm
  have hZ := mixedSeparated_Z_smooth J j q f hr τ lam hp hm
  have hYx := hY.angular_differentiableAt hΩ
  have hZx := hZ.angular_differentiableAt hΩ
  have hZfreeze : transport (mixedContourVelocity J j q f r τ lam) Z s θ = 0 := by
    rw [← mixedCoordinateTransport_eq_lie _ _ _ _ hZx]
    exact mixed_actual_Z_frozen J j q f hr τ lam s θ hj hΩ.1
      (fun _ => hp.differentiable (by simp) _) (fun _ => hm.differentiable (by simp) _)
      hplateau hΩ.2.1 hΩ.2.2.1 hΩ.2.2.2.1
  have hYfreeze : transport (mixedContourVelocity J j q f r τ lam) Y s θ = 0 := by
    rw [← mixedCoordinateTransport_eq_lie _ _ _ _ hYx]
    exact mixed_actual_Y_frozen J j q f hr τ lam s θ hj
      (fun _ => hp.differentiable (by simp) _) (fun _ => hm.differentiable (by simp) _) hplateau
  apply simpleKernel_frozen _ (fun t x => σ*Z t x) (fun t x => σ*Y t x) s θ
    ((hZ _ hΩ).2.const_mul σ) ((hY _ hΩ).2.const_mul σ)
    (hZx.const_mul σ) (hYx.const_mul σ)
    (signed_product_gap_ne_zero (Nat.succ_pos n) σ hσ _
      (fun i => interiorRoot_norm_lt_one (hΩ.2.1 i)))
    (signed_gap_ne_zero σ _ hσ (hYgap θ))
  · rw [IsingBulk.Tail.transport_const_mul _ Z σ s θ hZx,hZfreeze,mul_zero]
  · rw [IsingBulk.Tail.transport_const_mul _ Y σ s θ hYx,hYfreeze,mul_zero]

end
end IsingBulk.HT.Tail
