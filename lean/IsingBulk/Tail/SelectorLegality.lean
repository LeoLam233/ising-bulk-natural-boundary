import IsingBulk.Tail.SelectorDefinitions
import IsingBulk.Analysis.BranchLocal
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! Legality of the entire coupled real homotopy: every dispersion root
remains interior, despite lower y radii that can move outside the unit disk. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First
open scoped BigOperators

 theorem sourceW_polar_im (s : ℂ) (v θ : ℝ) :
    (sourceW s (Complex.exp ((v:ℂ)+(θ:ℂ)*Complex.I))).im =
      (sourceS s).im-Real.sinh v*Real.sin θ := by
  exact IsingBulk.Branch.polar_dispersion_im s v θ

 theorem radial_motion_im_mono (s : ℂ) (v θ h : ℝ) (hh : h*Real.sin θ ≤ 0) :
    (sourceW s (Complex.exp ((v:ℂ)+(θ:ℂ)*Complex.I))).im ≤
      (sourceW s (Complex.exp (((v+h:ℝ):ℂ)+(θ:ℂ)*Complex.I))).im := by
  rw [sourceW_polar_im, sourceW_polar_im]
  by_cases hp : 0 < h
  · have hs : Real.sin θ ≤ 0 := by nlinarith
    have hm := mul_le_mul_of_nonpos_right
      (Real.sinh_le_sinh.mpr (show v ≤ v+h by linarith)) hs
    linarith
  · by_cases hn : h < 0
    · have hs : 0 ≤ Real.sin θ := by nlinarith
      have hm := mul_le_mul_of_nonneg_right
        (Real.sinh_le_sinh.mpr (show v+h ≤ v by linarith)) hs
      linarith
    · have he : h=0 := by linarith
      simp [he]

 theorem retractionShift_sine_nonpos {N : ℕ} (hN : 0 < N) {τ : ℝ} (hτ : 0 ≤ τ)
    (f : SelectorFunctions) (θ : Fin N → ℝ)
    (hp : ∀ x, 0 ≤ f.p x) (hm : ∀ x, 0 ≤ f.m x)
    (hps : ∀ x, Real.sin x ≤ 0 → f.p x=0)
    (hms : ∀ x, 0 ≤ Real.sin x → f.m x=0) (i : Fin N) :
    retractionShift τ (fun j => f.p (θ j)) (fun j => f.m (θ j)) i*Real.sin (θ i) ≤ 0 := by
  have hn : (0:ℝ) < N := by exact_mod_cast hN
  have hP := occupancy_nonneg (fun i => hp (θ i))
  by_cases hs : 0 ≤ Real.sin (θ i)
  · simp only [retractionShift, hms _ hs, mul_zero, add_zero]
    have := mul_nonneg (hp (θ i)) hs
    nlinarith [mul_nonneg hτ this]
  · have hs' := (lt_of_not_ge hs).le
    simp only [retractionShift, hps _ hs', mul_zero, zero_add]
    have hmi := hm (θ i)
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hs'

 theorem deformedPoint_polar {N : ℕ} (f : SelectorFunctions) {r : ℝ} (hr : 0 < r)
    (τ lam : ℝ) (θ : Fin N → ℝ) (i : Fin N) :
    deformedPoint f r τ lam θ i = Complex.exp
      (((Real.log r+lam*retractionShift τ (fun j => f.p (θ j))
        (fun j => f.m (θ j)) i:ℝ):ℂ)+(θ i:ℂ)*Complex.I) := by
  unfold deformedPoint
  simp only [Complex.ofReal_add, Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hr]
  rw [mul_comm Complex.I (θ i:ℂ)]
  ring

 theorem deformed_sourceW_im_ge {N : ℕ} (hN : 0 < N)
    (f : SelectorFunctions) {r τ lam : ℝ} (hr : 0 < r) (hτ : 0 ≤ τ) (hlam : 0 ≤ lam)
    (θ : Fin N → ℝ) (s : ℂ)
    (hp : ∀ x, 0 ≤ f.p x) (hm : ∀ x, 0 ≤ f.m x)
    (hps : ∀ x, Real.sin x ≤ 0 → f.p x=0)
    (hms : ∀ x, 0 ≤ Real.sin x → f.m x=0) (i : Fin N) :
    (sourceW s (deformedPoint f r τ 0 θ i)).im ≤
      (sourceW s (deformedPoint f r τ lam θ i)).im := by
  rw [deformedPoint_polar f hr, deformedPoint_polar f hr]
  simp only [zero_mul, add_zero]
  apply radial_motion_im_mono
  rw [mul_assoc]
  exact mul_nonpos_of_nonneg_of_nonpos hlam (retractionShift_sine_nonpos hN hτ f θ hp hm hps hms i)

 theorem deformedPoint_zero_norm {N : ℕ} (f : SelectorFunctions) {r : ℝ}
    (hr : 0 ≤ r) (τ : ℝ) (θ : Fin N → ℝ) (i : Fin N) :
    ‖deformedPoint f r τ 0 θ i‖ = r := by
  simp [deformedPoint, Complex.norm_exp, abs_of_nonneg hr]

 theorem homotopy_root_interior {N : ℕ} (hN : 0 < N)
    (f : SelectorFunctions) {r τ lam : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hτ : 0 ≤ τ) (hlam : 0 ≤ lam) (θ : Fin N → ℝ) (s : ℂ)
    (hmargin : r⁻¹-r < (sourceS s).im)
    (hp : ∀ x, 0 ≤ f.p x) (hm : ∀ x, 0 ≤ f.m x)
    (hps : ∀ x, Real.sin x ≤ 0 → f.p x=0)
    (hms : ∀ x, 0 ≤ Real.sin x → f.m x=0) (i : Fin N) :
    ‖globalRoot s (deformedPoint f r τ lam θ i)‖ < 1 ∧
      (globalRoot s (deformedPoint f r τ lam θ i)).im < 0 := by
  have hbase := sourceW_upper_of_margin hr hr1 hmargin
    (deformedPoint_zero_norm f hr.le τ θ i)
  have hW := hbase.trans_le (deformed_sourceW_im_ge hN f hr hτ hlam θ s hp hm hps hms i)
  exact ⟨interiorRoot_norm_lt_one hW, interiorRoot_lower_im hW⟩

 theorem deformedPoint_norm {N : ℕ} (f : SelectorFunctions) {r : ℝ}
    (hr : 0 ≤ r) (τ lam : ℝ) (θ : Fin N → ℝ) (i : Fin N) :
    ‖deformedPoint f r τ lam θ i‖ =
      r*Real.exp (lam*retractionShift τ (fun j => f.p (θ j)) (fun j => f.m (θ j)) i) := by
  simp [deformedPoint, Complex.norm_exp, abs_of_nonneg hr]

 theorem deformed_product_norm {N : ℕ} (f : SelectorFunctions) {r : ℝ}
    (hr : 0 ≤ r) (τ lam : ℝ) (θ : Fin N → ℝ) :
    ‖coordinateProduct (deformedPoint f r τ lam θ)‖ =
      r^N*Real.exp (lam*∑ i, retractionShift τ (fun j => f.p (θ j)) (fun j => f.m (θ j)) i) := by
  simp only [coordinateProduct, norm_prod, deformedPoint_norm f hr,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← Real.exp_sum, Finset.mul_sum]

 theorem homotopy_y_product_lt_one {N : ℕ} (hN : 0 < N)
    (f : SelectorFunctions) {r τ lam : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hτ : 0 ≤ τ) (hlam : 0 ≤ lam) (θ : Fin N → ℝ)
    (hp : ∀ x, 0 ≤ f.p x) (hm : ∀ x, f.m x ≤ 1) :
    ‖coordinateProduct (deformedPoint f r τ lam θ)‖ < 1 := by
  rw [deformed_product_norm f hr.le]
  have hsum := sum_retractionShift_le hN hτ (fun i => hp (θ i)) (fun i => hm (θ i))
  have hP := occupancy_nonneg (fun i => hp (θ i))
  have hsum0 : (∑ i, retractionShift τ (fun j => f.p (θ j)) (fun j => f.m (θ j)) i) ≤ 0 := by
    nlinarith [mul_nonneg hτ hP]
  have he : Real.exp (lam*∑ i, retractionShift τ (fun j => f.p (θ j))
      (fun j => f.m (θ j)) i) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hlam hsum0)
  calc
    _ ≤ r^N*1 := mul_le_mul_of_nonneg_left he (pow_nonneg hr.le _)
    _ < 1 := by simpa using pow_lt_one₀ hr.le hr1 (Nat.ne_of_gt hN)

 theorem homotopy_y_gap_nonzero {N : ℕ} (hN : 0 < N)
    (f : SelectorFunctions) {r τ lam : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hτ : 0 ≤ τ) (hlam : 0 ≤ lam) (θ : Fin N → ℝ)
    (hp : ∀ x, 0 ≤ f.p x) (hm : ∀ x, f.m x ≤ 1) :
    1-coordinateProduct (deformedPoint f r τ lam θ) ≠ 0 := by
  have hlt := homotopy_y_product_lt_one hN f hr hr1 hτ hlam θ hp hm
  intro he
  have he' := (sub_eq_zero.mp he).symm
  rw [he', norm_one] at hlt
  exact lt_irrefl _ hlt

end
end IsingBulk.Tail
