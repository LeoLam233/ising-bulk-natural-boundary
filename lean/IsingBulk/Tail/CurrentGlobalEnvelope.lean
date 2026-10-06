import IsingBulk.Tail.SelectedGlobalEnvelope
import IsingBulk.Tail.ConstructedCurrentDisk

/-! Explicit uniform current envelopes. The temporary deformation strength
lambda*tau is eliminated from every final constant. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch
open scoped BigOperators

theorem current_y_norm_envelope {N : ℕ} (hN : 0 < N) (f : SelectorFunctions)
    {c₀ τ eps lam : ℝ} (hc : 0 ≤ c₀) (hτ : 0 ≤ τ) (heps : 0 ≤ eps) (heps1 : eps ≤ 1)
    (hlam : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hp0 : ∀ x, 0 ≤ f.p x) (hp1 : ∀ x, f.p x ≤ 1)
    (hm0 : ∀ x, 0 ≤ f.m x) (hm1 : ∀ x, f.m x ≤ 1)
    (θ : Fin N → ℝ) (i : Fin N) :
    ‖deformedPoint f (Real.exp (-c₀*eps)) τ lam θ i‖ ≤ Real.exp (c₀+2*τ) ∧
    ‖(deformedPoint f (Real.exp (-c₀*eps)) τ lam θ i)⁻¹‖ ≤ Real.exp (c₀+2*τ) := by
  rw [deformedPoint_scale_lambda]
  have hh := selected_y_norm_envelope hN f hc (mul_nonneg hlam hτ) heps heps1 hp0 hp1 hm0 hm1 θ i
  have ht : Real.exp (c₀+2*(lam*τ)) ≤ Real.exp (c₀+2*τ) :=
    Real.exp_le_exp.mpr (by nlinarith)
  exact ⟨hh.1.trans ht,hh.2.trans ht⟩

theorem current_actual_inverse_numerator {N : ℕ} (hN : 1 ≤ N)
    (f : SelectorFunctions) {c₀ τ eps c θ₀ lamStar lam : ℝ}
    (hc₀ : 0 ≤ c₀) (hτ : 0 ≤ τ) (heps : 0 ≤ eps) (heps1 : eps ≤ 1)
    (hc0 : 0 ≤ c) (hc : c ≤ 1/4) (hls : 0 ≤ lamStar) (hl : lamStar ≤ lam) (hl1 : lam ≤ 1)
    (hp0 : ∀ x, 0 ≤ f.p x) (hp1 : ∀ x, f.p x ≤ 1)
    (hm0 : ∀ x, 0 ≤ f.m x) (hm1 : ∀ x, f.m x ≤ 1)
    (θ : Fin N → ℝ) {s : ℂ}
    (hs : ‖s-radialParameter θ₀ eps‖ ≤ c*lamStar/(N:ℝ)^2) :
    let y := deformedPoint f (Real.exp (-c₀*eps)) τ lam θ
    let z := fun i => selectedContinuedRoot s (y i)
    ‖(coordinateProduct z)⁻¹+(coordinateProduct y)⁻¹‖ ≤
      2*(21+4*Real.exp (c₀+2*τ))^N := by
  have hn : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (0:ℝ)<N := by linarith
  have hrad : c*lamStar/(N:ℝ)^2 ≤ c/(N:ℝ) := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hn0) hn0).mpr
    have hh : lamStar ≤ (N:ℝ) := (hl.trans hl1).trans hn
    nlinarith [mul_nonneg hc0 (sub_nonneg.mpr hh)]
  have he : deformedPoint f (Real.exp (-c₀*eps)) τ lam θ =
      deformedPoint f (Real.exp (-c₀*eps)) (lam*τ) 1 θ :=
    funext (deformedPoint_scale_lambda f _ τ lam θ)
  dsimp only
  rw [he]
  have hb := selected_actual_inverse_numerator hN f hc₀ (mul_nonneg (hls.trans hl) hτ)
    heps heps1 hc hp0 hp1 hm0 hm1 θ (hs.trans hrad)
  apply hb.trans
  gcongr
  nlinarith


/-- The two actual product gaps cost lambda squared, uniformly up to 1. -/
theorem current_global_denominator_lower {a b lam : ℝ} {Z Y : ℂ}
    (ha : 0<a) (hb : 0<b) (hlam : 0≤lam) (hlam1 : lam≤1)
    (hZ : ‖Z‖ ≤ Real.exp (-a*lam)) (hY : ‖Y‖ ≤ Real.exp (-b*lam)) :
    (a*b*Real.exp (-(a+b)))*lam^2 ≤ ‖(1-Z)*(1-Y)‖ := by
  have hz := exponential_attenuation_linear_gap ha.le hlam hlam1 hZ
  have hy := exponential_attenuation_linear_gap hb.le hlam hlam1 hY
  have hh := mul_le_mul hz hy (by positivity : 0≤b*Real.exp (-b)*lam) (norm_nonneg (1-Z))
  rw [norm_mul]
  calc
    _ = (a*Real.exp (-a)*lam)*(b*Real.exp (-b)*lam) := by
      rw [neg_add,Real.exp_add]
      ring
    _ ≤ _ := hh

end
end IsingBulk.Tail
