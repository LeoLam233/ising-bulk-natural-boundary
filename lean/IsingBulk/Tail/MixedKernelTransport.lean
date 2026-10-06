import IsingBulk.Tail.MixedFreezeCalculus
import IsingBulk.Tail.MixedSeparatedDensity

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set Filter
open scoped Topology BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false

def mixedSimpleKernel {N : ℕ} (f : SelectorFunctions) (r τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ) : ℂ :=
  (1-coordinateProduct (fun i => globalRoot s (deformedPoint f r τ lam θ i)))⁻¹*
    (1-coordinateProduct (deformedPoint f r τ lam θ))⁻¹

theorem mixedSeparated_Y_smooth {N : ℕ} (J : Finset (Fin N)) (j q : Fin N)
    (f : SelectorFunctions) (r τ lam : ℝ) (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m) :
    ParameterSmoothOn (mixedSeparatedDomain J j q f r τ lam)
      (fun _ θ => coordinateProduct (deformedPoint f r τ lam θ)) :=
  ParameterSmoothOn.prod Finset.univ _ (fun i _ => mixedSeparated_y_smooth J j q f r τ lam hp hm i)

theorem mixedSeparated_Z_smooth {N : ℕ} (J : Finset (Fin N)) (j q : Fin N)
    (f : SelectorFunctions) {r : ℝ} (hr : 0<r) (τ lam : ℝ) (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m) :
    ParameterSmoothOn (mixedSeparatedDomain J j q f r τ lam)
      (fun s θ => coordinateProduct (fun i => globalRoot s (deformedPoint f r τ lam θ i))) :=
  ParameterSmoothOn.prod Finset.univ _ (fun i _ => mixedSeparated_root_smooth J j q f hr τ lam hp hm i)

theorem mixedSeparated_kernel_smooth {N : ℕ} (hN : 0<N) (J : Finset (Fin N)) (j q : Fin N)
    (f : SelectorFunctions) {r : ℝ} (hr : 0<r) (τ lam : ℝ) (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m) :
    ParameterSmoothOn (mixedSeparatedDomain J j q f r τ lam) (mixedSimpleKernel f r τ lam) := by
  have hY := mixedSeparated_Y_smooth J j q f r τ lam hp hm
  have hZ := mixedSeparated_Z_smooth J j q f hr τ lam hp hm
  exact (((ParameterSmoothOn.const _ 1).sub hZ).inv (fun p h =>
    one_sub_coordinateProduct_ne_zero hN (fun i => interiorRoot_norm_lt_one (h.2.1 i)))).mul
    (((ParameterSmoothOn.const _ 1).sub hY).inv (fun _ h => h.2.2.2.2))

/-- The actual two simple poles are frozen by the source transport field.
Their nonvanishing is proved on the same separated source domain. -/
theorem mixed_actual_kernel_frozen {n : ℕ} (J : Finset (Fin (n+1))) (j q : Fin (n+1))
    (f : SelectorFunctions) {r : ℝ} (hr : 0<r) (τ lam : ℝ) (s : ℂ) (θ : Fin (n+1) → ℝ)
    (hj : j∈J) (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m)
    (hplateau : ∀ i,i∈J ∨ i=q → deriv f.p (θ i)=0 ∧ deriv f.m (θ i)=0)
    (hΩ : (s,θ)∈mixedSeparatedDomain J j q f r τ lam) :
    mixedCoordinateTransport (mixedContourVelocity J j q f r τ lam) (mixedSimpleKernel f r τ lam) s θ=0 := by
  let Y := fun (_ : ℂ) (x : Fin (n+1) → ℝ) => coordinateProduct (deformedPoint f r τ lam x)
  let Z := fun (z : ℂ) (x : Fin (n+1) → ℝ) => coordinateProduct (fun i => globalRoot z (deformedPoint f r τ lam x i))
  have hY := mixedSeparated_Y_smooth J j q f r τ lam hp hm
  have hZ := mixedSeparated_Z_smooth J j q f hr τ lam hp hm
  have hYx := hY.angular_differentiableAt hΩ
  have hZx := hZ.angular_differentiableAt hΩ
  have hKx := (mixedSeparated_kernel_smooth (Nat.succ_pos n) J j q f hr τ lam hp hm).angular_differentiableAt hΩ
  rw [mixedCoordinateTransport_eq_lie _ _ _ _ hKx]
  apply IsingBulk.Lie.simpleKernel_frozen _ Z Y s θ (hZ _ hΩ).2 (hY _ hΩ).2 hZx hYx
    (one_sub_coordinateProduct_ne_zero (Nat.succ_pos n) (fun i => interiorRoot_norm_lt_one (hΩ.2.1 i))) hΩ.2.2.2.2
  · rw [← mixedCoordinateTransport_eq_lie _ _ _ _ hZx]
    exact mixed_actual_Z_frozen J j q f hr τ lam s θ hj hΩ.1
      (fun _ => hp.differentiable (by simp) _) (fun _ => hm.differentiable (by simp) _)
      hplateau hΩ.2.1 hΩ.2.2.1 hΩ.2.2.2.1
  · rw [← mixedCoordinateTransport_eq_lie _ _ _ _ hYx]
    exact mixed_actual_Y_frozen J j q f hr τ lam s θ hj
      (fun _ => hp.differentiable (by simp) _) (fun _ => hm.differentiable (by simp) _) hplateau

end
end IsingBulk.Tail
