import IsingBulk.Analysis.LieIntegration
import Mathlib.Analysis.Calculus.Deriv.Inv

/-! Pointwise analytic transport on complex parameter / real angular coordinates.
The vector-field coefficients are functions of the parameter throughout. -/
namespace IsingBulk.Lie
noncomputable section
open scoped BigOperators

def transport {n : ℕ} (V : ℂ → AngularSpace n → Fin (n+1) → ℂ)
    (A : ℂ → AngularSpace n → ℂ) (s : ℂ) (x : AngularSpace n) : ℂ :=
  deriv (fun t => A t x) s -
    ∑ i, V s x i * fderiv ℝ (A s) x (Pi.single i 1)

theorem lieStep_eq_transport_sub {n : ℕ}
    (V : ℂ → AngularSpace n → Fin (n+1) → ℂ) (A : ℂ → AngularSpace n → ℂ)
    (s : ℂ) (x : AngularSpace n)
    (hV : ∀ i, DifferentiableAt ℝ (fun y => V s y i) x)
    (hA : DifferentiableAt ℝ (A s) x) :
    lieStep V A s x = transport V A s x - divergence (V s) x * A s x := by
  simp only [lieStep, transport, divergence]
  simp_rw [fderiv_fun_mul (hV _) hA]
  simp only [add_apply, smul_apply,
    smul_eq_mul, Finset.sum_add_distrib, Finset.sum_mul]
  ring_nf

theorem transport_mul {n : ℕ} (V : ℂ → AngularSpace n → Fin (n+1) → ℂ)
    (A B : ℂ → AngularSpace n → ℂ) (s : ℂ) (x : AngularSpace n)
    (hAs : DifferentiableAt ℂ (fun t => A t x) s)
    (hBs : DifferentiableAt ℂ (fun t => B t x) s)
    (hAx : DifferentiableAt ℝ (A s) x) (hBx : DifferentiableAt ℝ (B s) x) :
    transport V (fun t y => A t y * B t y) s x =
      transport V A s x * B s x + A s x * transport V B s x := by
  simp only [transport, deriv_fun_mul hAs hBs, fderiv_fun_mul hAx hBx,
    add_apply, smul_apply, smul_eq_mul]
  have hsum : (∑ i, V s x i * (A s x * fderiv ℝ (B s) x (Pi.single i 1) +
      B s x * fderiv ℝ (A s) x (Pi.single i 1))) =
      (∑ i, V s x i * fderiv ℝ (A s) x (Pi.single i 1)) * B s x +
      A s x * ∑ i, V s x i * fderiv ℝ (B s) x (Pi.single i 1) := by
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intros
    ring
  rw [hsum]
  ring

theorem transport_inv {n : ℕ} (V : ℂ → AngularSpace n → Fin (n+1) → ℂ)
    (A : ℂ → AngularSpace n → ℂ) (s : ℂ) (x : AngularSpace n)
    (hAs : DifferentiableAt ℂ (fun t => A t x) s)
    (hAx : DifferentiableAt ℝ (A s) x) (hne : A s x ≠ 0) :
    transport V (fun t y => (A t y)⁻¹) s x = -(A s x)^(-2:ℤ) * transport V A s x := by
  have hxinv := ((hasFDerivAt_inv' (𝕜 := ℝ) hne).comp x hAx.hasFDerivAt).fderiv
  have hxval : ∀ e, fderiv ℝ (fun y => (A s y)⁻¹) x e =
      -(A s x ^ 2)⁻¹ * fderiv ℝ (A s) x e := by
    intro e
    rw [show (fun y => (A s y)⁻¹) = Inv.inv ∘ A s from rfl, hxinv]
    simp only [ContinuousLinearMap.comp_apply, neg_apply,
      ContinuousLinearMap.mulLeftRight_apply]
    ring
  simp only [transport, deriv_fun_inv'' hAs hne, hxval]
  simp only [zpow_neg, zpow_ofNat]
  simp_rw [div_eq_mul_inv]
  rw [show (∑ i, V s x i * (-(A s x ^ 2)⁻¹ *
      fderiv ℝ (A s) x (Pi.single i 1))) =
      -(A s x ^ 2)⁻¹ * ∑ i, V s x i * fderiv ℝ (A s) x (Pi.single i 1) by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring]
  ring

/-- This is the concrete pointwise product identity behind densityOperator's
frozen-factor rule; it follows from the actual parameter/spatial derivatives. -/
theorem lieStep_mul_frozen {n : ℕ} (V : ℂ → AngularSpace n → Fin (n+1) → ℂ)
    (K A : ℂ → AngularSpace n → ℂ) (s : ℂ) (x : AngularSpace n)
    (hKs : DifferentiableAt ℂ (fun t => K t x) s)
    (hAs : DifferentiableAt ℂ (fun t => A t x) s)
    (hKx : DifferentiableAt ℝ (K s) x) (hAx : DifferentiableAt ℝ (A s) x)
    (hV : ∀ i, DifferentiableAt ℝ (fun y => V s y i) x)
    (hfreeze : transport V K s x = 0) :
    lieStep V (fun t y => K t y * A t y) s x = K s x * lieStep V A s x := by
  rw [lieStep_eq_transport_sub V _ s x hV (hKx.mul hAx),
    transport_mul V K A s x hKs hAs hKx hAx, hfreeze,
    lieStep_eq_transport_sub V A s x hV hAx]
  ring

theorem transport_one_sub {n : ℕ} (V : ℂ → AngularSpace n → Fin (n+1) → ℂ)
    (A : ℂ → AngularSpace n → ℂ) (s : ℂ) (x : AngularSpace n) :
    transport V (fun t y => 1-A t y) s x = -transport V A s x := by
  simp only [transport, deriv_const_sub, fderiv_const_sub, neg_apply,
    mul_neg, Finset.sum_neg_distrib]
  ring

def simpleKernel {n : ℕ} (Y Z : ℂ → AngularSpace n → ℂ) (s : ℂ)
    (x : AngularSpace n) : ℂ := (1-Y s x)⁻¹*(1-Z s x)⁻¹

/-- Freezing is now stated for the source transport derivative itself. -/
theorem simpleKernel_frozen {n : ℕ} (V : ℂ → AngularSpace n → Fin (n+1) → ℂ)
    (Y Z : ℂ → AngularSpace n → ℂ) (s : ℂ) (x : AngularSpace n)
    (hYs : DifferentiableAt ℂ (fun t => Y t x) s)
    (hZs : DifferentiableAt ℂ (fun t => Z t x) s)
    (hYx : DifferentiableAt ℝ (Y s) x) (hZx : DifferentiableAt ℝ (Z s) x)
    (hY1 : 1-Y s x ≠ 0) (hZ1 : 1-Z s x ≠ 0)
    (hY : transport V Y s x = 0) (hZ : transport V Z s x = 0) :
    transport V (simpleKernel Y Z) s x = 0 := by
  unfold simpleKernel
  rw [transport_mul V _ _ s x ((hYs.const_sub 1).inv hY1) ((hZs.const_sub 1).inv hZ1)
    ((hYx.const_sub 1).inv hY1) ((hZx.const_sub 1).inv hZ1)]
  rw [transport_inv V _ s x (hYs.const_sub 1) (hYx.const_sub 1) hY1,
    transport_inv V _ s x (hZs.const_sub 1) (hZx.const_sub 1) hZ1,
    transport_one_sub, transport_one_sub, hY, hZ]
  ring

/-- Concrete analytic iteration of a frozen factor. Global differentiability
is explicit in this interface; no smoothness at a pole is inferred. -/
theorem iterate_lieStep_mul_frozen {n : ℕ}
    (V : ℂ → AngularSpace n → Fin (n+1) → ℂ) (K A : ℂ → AngularSpace n → ℂ)
    (hKs : ∀ s x, DifferentiableAt ℂ (fun t => K t x) s)
    (hKx : ∀ s x, DifferentiableAt ℝ (K s) x)
    (hV : ∀ s x i, DifferentiableAt ℝ (fun y => V s y i) x)
    (hfreeze : ∀ s x, transport V K s x = 0) (j : ℕ)
    (hAs : ∀ k < j, ∀ s x, DifferentiableAt ℂ (fun t => ((lieStep V)^[k] A) t x) s)
    (hAx : ∀ k < j, ∀ s x, DifferentiableAt ℝ (((lieStep V)^[k] A) s) x) :
    (lieStep V)^[j] (fun s x => K s x*A s x) =
      fun s x => K s x*((lieStep V)^[j] A) s x := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih
      (fun k hk => hAs k (by omega)) (fun k hk => hAx k (by omega))]
    funext s x
    rw [Function.iterate_succ_apply']
    exact lieStep_mul_frozen V K _ s x (hKs s x) (hAs j (by omega) s x)
      (hKx s x) (hAx j (by omega) s x) (hV s x) (hfreeze s x)

/-- Full product rule, including the cutoff descendant omitted by a frozen
weight argument. -/
theorem lieStep_product_rule {n : ℕ} (V : ℂ → AngularSpace n → Fin (n+1) → ℂ)
    (K A : ℂ → AngularSpace n → ℂ) (s : ℂ) (x : AngularSpace n)
    (hKs : DifferentiableAt ℂ (fun t => K t x) s)
    (hAs : DifferentiableAt ℂ (fun t => A t x) s)
    (hKx : DifferentiableAt ℝ (K s) x) (hAx : DifferentiableAt ℝ (A s) x)
    (hV : ∀ i, DifferentiableAt ℝ (fun y => V s y i) x) :
    lieStep V (fun t y => K t y * A t y) s x =
      K s x * lieStep V A s x + transport V K s x * A s x := by
  rw [lieStep_eq_transport_sub V _ s x hV (hKx.mul hAx),
    transport_mul V K A s x hKs hAs hKx hAx,
    lieStep_eq_transport_sub V A s x hV hAx]
  ring

/-- Real fixed cutoffs are differentiated on the real domain only. -/
theorem lieStep_real_weight {n : ℕ} (V : ℂ → AngularSpace n → Fin (n+1) → ℂ)
    (w : AngularSpace n → ℝ) (A : ℂ → AngularSpace n → ℂ)
    (s : ℂ) (x : AngularSpace n) (hw : DifferentiableAt ℝ w x)
    (hAs : DifferentiableAt ℂ (fun t => A t x) s)
    (hAx : DifferentiableAt ℝ (A s) x)
    (hV : ∀ i, DifferentiableAt ℝ (fun y => V s y i) x) :
    lieStep V (fun t y => (w y:ℂ)*A t y) s x =
      (w x:ℂ)*lieStep V A s x -
      (∑ i, V s x i * (fderiv ℝ w x (Pi.single i 1):ℂ))*A s x := by
  have hwc := Complex.ofRealCLM.hasFDerivAt.comp x hw.hasFDerivAt
  rw [lieStep_product_rule V (fun _ y => (w y:ℂ)) A s x
    (differentiableAt_const _) hAs hwc.differentiableAt hAx hV]
  have he : ∀ e, fderiv ℝ (fun y => (w y:ℂ)) x e = (fderiv ℝ w x e:ℂ) := by
    intro e
    change fderiv ℝ (Complex.ofRealCLM ∘ w) x e = (fderiv ℝ w x e:ℂ)
    rw [hwc.fderiv]
    rfl
  simp only [transport, deriv_const, he, zero_sub]
  ring

end
end IsingBulk.Lie


