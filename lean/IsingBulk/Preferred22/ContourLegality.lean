import IsingBulk.Preferred22.Contour
import IsingBulk.Preferred22.PhysicalAnalytic
import IsingBulk.Analysis.BranchLocal
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! LT22 Section 5: legality of the literal balanced whole-contour homotopy. -/
namespace IsingBulk.Preferred22
noncomputable section
open scoped BigOperators ContDiff Topology
open Set Filter MeasureTheory

def complexW (s y : ℂ) : ℂ := temperatureTrace s - (y+y⁻¹)/2

theorem physicalRoot_differentiableAt_upper {W : ℂ} (hW : 0 < W.im) :
    DifferentiableAt ℂ physicalRoot W :=
  (physicalRoot_analyticAt (Or.inl hW.ne')).differentiableAt

theorem complexW_polar_im (s : ℂ) (v θ : ℝ) :
    (complexW s (Complex.exp ((v:ℂ)+(θ:ℂ)*Complex.I))).im =
      (temperatureTrace s).im - Real.sinh v*Real.sin θ := by
  exact IsingBulk.Branch.polar_dispersion_im s v θ

theorem balancedShift_sine_nonpos {N : ℕ} {τ : ℝ} (hτ : 0 ≤ τ)
    (p m : ℝ → ℝ) (θ : Fin N → ℝ)
    (hp0 : ∀ x, 0 ≤ p x) (hm0 : ∀ x, 0 ≤ m x)
    (hps : ∀ x, Real.sin x ≤ 0 → p x=0)
    (hms : ∀ x, 0 ≤ Real.sin x → m x=0) (i : Fin N) :
    balancedShift τ p m θ i*Real.sin (θ i) ≤ 0 := by
  have hP : 0 ≤ occupancy p θ := Finset.sum_nonneg (fun j _ => hp0 (θ j))
  have hQ : 0 ≤ occupancy m θ := Finset.sum_nonneg (fun j _ => hm0 (θ j))
  unfold balancedShift
  rw [mul_assoc]
  apply mul_nonpos_of_nonneg_of_nonpos (div_nonneg hτ (Nat.cast_nonneg N))
  by_cases hs : 0 ≤ Real.sin (θ i)
  · rw [hms _ hs, mul_zero, zero_sub]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (mul_nonneg hQ (hp0 _))) hs
  · rw [hps _ (le_of_not_ge hs), mul_zero, sub_zero]
    exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hP (hm0 _)) (le_of_not_ge hs)

theorem homotopy_complexW_im_ge {N : ℕ} {s : ℂ}
    {τ lam : ℝ}
    (hτ : 0 ≤ τ) (hlam : 0 ≤ lam) (p m : ℝ → ℝ) (θ : Fin N → ℝ)
    (hp0 : ∀ x, 0 ≤ p x) (hm0 : ∀ x, 0 ≤ m x)
    (hps : ∀ x, Real.sin x ≤ 0 → p x=0)
    (hms : ∀ x, 0 ≤ Real.sin x → m x=0) (i : Fin N) :
    (temperatureTrace s).im ≤ (complexW s (homotopyRoot τ lam p m θ i)).im := by
  have hh := balancedShift_sine_nonpos hτ p m θ hp0 hm0 hps hms i
  have hv : (lam*balancedShift τ p m θ i)*Real.sin (θ i) ≤ 0 := by
    rw [mul_assoc]
    exact mul_nonpos_of_nonneg_of_nonpos hlam hh
  have hpolar : homotopyRoot τ lam p m θ i =
      Complex.exp (((lam*balancedShift τ p m θ i:ℝ):ℂ)+(θ i:ℂ)*Complex.I) := by
    unfold homotopyRoot
    congr 1
    push_cast
    ring
  rw [hpolar, complexW_polar_im]
  have hsinh : Real.sinh (lam*balancedShift τ p m θ i)*Real.sin (θ i) ≤ 0 := by
    by_cases hp : 0 < lam*balancedShift τ p m θ i
    · have hs : Real.sin (θ i) ≤ 0 := by nlinarith
      exact mul_nonpos_of_nonneg_of_nonpos (Real.sinh_nonneg_iff.mpr hp.le) hs
    · have hp' := le_of_not_gt hp
      by_cases hn : lam*balancedShift τ p m θ i < 0
      · have hs : 0 ≤ Real.sin (θ i) := by nlinarith
        exact mul_nonpos_of_nonpos_of_nonneg (Real.sinh_nonpos_iff.mpr hp') hs
      · have hz : lam*balancedShift τ p m θ i=0 := le_antisymm hp' (le_of_not_gt hn)
        simp [hz]
  linarith

theorem homotopy_complexW_im_pos {N : ℕ} {s : ℂ}
    (hS : 0 < (temperatureTrace s).im) {τ lam : ℝ}
    (hτ : 0 ≤ τ) (hlam : 0 ≤ lam) (p m : ℝ → ℝ) (θ : Fin N → ℝ)
    (hp0 : ∀ x, 0 ≤ p x) (hm0 : ∀ x, 0 ≤ m x)
    (hps : ∀ x, Real.sin x ≤ 0 → p x=0)
    (hms : ∀ x, 0 ≤ Real.sin x → m x=0) (i : Fin N) :
    0 < (complexW s (homotopyRoot τ lam p m θ i)).im :=
  hS.trans_le (homotopy_complexW_im_ge hτ hlam p m θ hp0 hm0 hps hms i)

/-- All pair and product denominators remain nonzero throughout
the entire balanced homotopy, before imposing a localization weight. -/
theorem homotopy_denominators {N : ℕ} (hN : 0 < N) {s : ℂ}
    (hS : 0 < (temperatureTrace s).im) {τ lam : ℝ}
    (hτ : 0 ≤ τ) (hlam : 0 ≤ lam) (p m : ℝ → ℝ) (θ : Fin N → ℝ)
    (hp0 : ∀ x, 0 ≤ p x) (hm0 : ∀ x, 0 ≤ m x)
    (hps : ∀ x, Real.sin x ≤ 0 → p x=0)
    (hms : ∀ x, 0 ≤ Real.sin x → m x=0) :
    let z := fun i => physicalRoot (complexW s (homotopyRoot τ lam p m θ i))
    (∀ i, ‖z i‖ < 1) ∧ (∀ i j, 1-z i*z j ≠ 0) ∧ 1-∏ i, z i ≠ 0 := by
  dsimp only
  let z := fun i => physicalRoot (complexW s (homotopyRoot τ lam p m θ i))
  have hzi : ∀ i, ‖z i‖ < 1 := fun i => physicalRoot_inside (Or.inl
    (homotopy_complexW_im_pos hS hτ hlam p m θ hp0 hm0 hps hms i).ne')
  refine ⟨hzi, ?_, ?_⟩
  · intro i j he
    have hprod : z i*z j=1 := (sub_eq_zero.mp he).symm
    have hh : ‖z i*z j‖ < 1 := by
      rw [norm_mul]
      calc
        ‖z i‖*‖z j‖ ≤ ‖z i‖*1 := mul_le_mul_of_nonneg_left (hzi j).le (norm_nonneg _)
        _ < 1 := by simpa using hzi i
    simp [hprod] at hh
  · have hprod : ‖∏ i, z i‖ < 1 := by
      rw [norm_prod]
      calc
        _ < ∏ _i : Fin N, (1:ℝ) := Finset.prod_lt_prod_of_nonempty₀
          (fun i _ => norm_pos_iff.mpr (physicalRoot_ne_zero _))
          (fun i _ => hzi i) ⟨⟨0,hN⟩, Finset.mem_univ _⟩
        _ = 1 := by simp
    intro he
    have hz : (∏ i, z i)=1 := (sub_eq_zero.mp he).symm
    simp [hz] at hprod

theorem complexW_exp_I (s w : ℂ) :
    complexW s (Complex.exp (Complex.I*w)) = temperatureTrace s - Complex.cos w := by
  have ht : Complex.exp (Complex.I*w)+(Complex.exp (Complex.I*w))⁻¹ = 2*Complex.cos w := by
    rw [← Complex.exp_neg]
    simpa only [mul_comm Complex.I w, neg_mul] using (Complex.two_cos w).symm
  rw [complexW, ht]
  ring

theorem homotopyRoot_eq_exp_deformedAngles {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (θ : Fin N → ℝ) (i : Fin N) :
    homotopyRoot τ 1 p m θ i = Complex.exp (Complex.I*deformedAngles τ p m θ i) := by
  unfold homotopyRoot deformedAngles
  congr 1
  simp only [Complex.ofReal_one, one_mul, mul_sub, ← mul_assoc, Complex.I_mul_I]
  ring

theorem complexW_homotopyRoot_eq {N : ℕ} (s : ℂ) (τ : ℝ) (p m : ℝ → ℝ)
    (θ : Fin N → ℝ) (i : Fin N) :
    complexW s (homotopyRoot τ 1 p m θ i) =
      temperatureTrace s - Complex.cos (deformedAngles τ p m θ i) := by
  rw [homotopyRoot_eq_exp_deformedAngles, complexW_exp_I]

end
end IsingBulk.Preferred22
