import IsingBulk.Preferred22.ContourLegality
import IsingBulk.Preferred22.ContourMatrix

/-!
# HT22: signed affine constrained homotopy foundations

The balanced displacement is literally identical to the already proved finite
dimensional displacement.  The additions here retain an arbitrary constraint
angle and an arbitrary unit-modulus total-product sign.  No coefficient,
tail estimate or natural-boundary theorem from LT22 or original HT is used.
-/

namespace IsingBulk.HT22.Geometry
noncomputable section
open scoped BigOperators
open IsingBulk.Preferred22

/-- Eliminate the last angle on the actual affine constraint, including π. -/
def signedAngles {n : ℕ} (a : ℝ) (θ : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  Fin.snoc θ (a - ∑ i, θ i)

theorem signedAngles_sum {n : ℕ} (a : ℝ) (θ : Fin n → ℝ) :
    ∑ i, signedAngles a θ i = a := by
  rw [Fin.sum_univ_castSucc]
  simp only [signedAngles, Fin.snoc_castSucc, Fin.snoc_last]
  ring

theorem signedAngles_reflect {n : ℕ} (a : ℝ) (θ : Fin n → ℝ) :
    signedAngles (-a) (fun i => -θ i) = fun i => -signedAngles a θ i := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [signedAngles, Finset.sum_neg_distrib]
    ring
  · simp [signedAngles]

/-- The actual angular homotopy, before a localization weight is inserted. -/
def homotopyAngles {N : ℕ} (τ lam : ℝ) (p m : ℝ → ℝ)
    (θ : Fin N → ℝ) (i : Fin N) : ℂ :=
  (θ i : ℂ) - Complex.I * (lam : ℂ) * (balancedShift τ p m θ i : ℂ)

theorem homotopyAngles_sum {N : ℕ} (τ lam : ℝ) (p m : ℝ → ℝ)
    (θ : Fin N → ℝ) :
    ∑ i, homotopyAngles τ lam p m θ i = ∑ i, (θ i : ℂ) := by
  simp only [homotopyAngles, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Complex.ofReal_sum, balancedShift_sum, Complex.ofReal_zero, mul_zero, sub_zero]

theorem signed_homotopy_sum {n : ℕ} (a τ lam : ℝ) (p m : ℝ → ℝ)
    (θ : Fin n → ℝ) :
    ∑ i, homotopyAngles τ lam p m (signedAngles a θ) i = (a : ℂ) := by
  rw [homotopyAngles_sum, ← Complex.ofReal_sum, signedAngles_sum]

theorem homotopyRoot_eq_exp_angle {N : ℕ} (τ lam : ℝ) (p m : ℝ → ℝ)
    (θ : Fin N → ℝ) (i : Fin N) :
    homotopyRoot τ lam p m θ i = Complex.exp (Complex.I * homotopyAngles τ lam p m θ i) := by
  unfold homotopyRoot homotopyAngles
  congr 1
  simp only [mul_sub, ← mul_assoc, Complex.I_mul_I]
  ring

/-- The signed constraint is preserved at every homotopy time. -/
theorem signed_homotopy_product {n : ℕ} (a τ lam : ℝ) (p m : ℝ → ℝ)
    (θ : Fin n → ℝ) :
    ∏ i, homotopyRoot τ lam p m (signedAngles a θ) i =
      Complex.exp (Complex.I * (a : ℂ)) := by
  rw [homotopy_product_preserved, ← Complex.exp_sum, ← Finset.mul_sum,
    ← Complex.ofReal_sum, signedAngles_sum]

/-- Unit-modulus signs do not change the interior-root product gap. -/
theorem unit_signed_product_gap {N : ℕ} (hN : 0 < N)
    (z : Fin N → ℂ) (hz : ∀ i, z i ≠ 0) (hzi : ∀ i, ‖z i‖ < 1)
    (σ : ℂ) (hσ : ‖σ‖ = 1) : 1 - σ * ∏ i, z i ≠ 0 := by
  have hprod : ‖∏ i, z i‖ < 1 := by
    rw [norm_prod]
    calc
      _ < ∏ _i : Fin N, (1 : ℝ) := Finset.prod_lt_prod_of_nonempty₀
        (fun i _ => norm_pos_iff.mpr (hz i)) (fun i _ => hzi i)
        ⟨⟨0, hN⟩, Finset.mem_univ _⟩
      _ = 1 := by simp
  intro he
  have heq : σ * ∏ i, z i = 1 := (sub_eq_zero.mp he).symm
  have hn := congrArg norm heq
  rw [norm_mul, hσ, one_mul, norm_one] at hn
  exact (ne_of_lt hprod) hn

/-- Both signed global denominators and every pair denominator survive the
whole balanced homotopy.  There are no weights in this statement. -/
theorem signed_homotopy_denominators {N : ℕ} (hN : 0 < N) {t : ℂ}
    (hS : 0 < (temperatureTrace t).im) {τ lam : ℝ}
    (hτ : 0 ≤ τ) (hlam : 0 ≤ lam) (p m : ℝ → ℝ) (θ : Fin N → ℝ)
    (hp0 : ∀ x, 0 ≤ p x) (hm0 : ∀ x, 0 ≤ m x)
    (hps : ∀ x, Real.sin x ≤ 0 → p x = 0)
    (hms : ∀ x, 0 ≤ Real.sin x → m x = 0)
    (σ : ℂ) (hσ : ‖σ‖ = 1) :
    let z := fun i => physicalRoot (complexW t (homotopyRoot τ lam p m θ i))
    (∀ i, ‖z i‖ < 1) ∧ (∀ i j, 1 - z i * z j ≠ 0) ∧
      (∀ i, z i ≠ 0) ∧ 1 - σ * ∏ i, z i ≠ 0 := by
  obtain ⟨hzi, hpairs, _⟩ :=
    homotopy_denominators hN hS hτ hlam p m θ hp0 hm0 hps hms
  refine ⟨hzi, hpairs, fun _ => physicalRoot_ne_zero _, ?_⟩
  exact unit_signed_product_gap hN _ (fun _ => physicalRoot_ne_zero _) hzi σ hσ

/-- Restriction to an affine sum constraint has the same tangent map as its
parallel zero-sum hyperplane.  This is the homotopy Jacobian, not the later
regular-coordinate scalar density Jχ. -/
def signedTangentJacobian {n : ℕ} (a τ lam : ℝ) (p m : ℝ → ℝ)
    (θ : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j =>
    fullAngularJacobian τ lam p m (signedAngles a θ) i.castSucc j.castSucc -
      fullAngularJacobian τ lam p m (signedAngles a θ) i.castSucc (Fin.last n)

theorem signedTangentJacobian_det {n : ℕ} (a τ lam : ℝ) (p m : ℝ → ℝ)
    (θ : Fin n → ℝ) :
    (signedTangentJacobian a τ lam p m θ).det =
      (fullAngularJacobian τ lam p m (signedAngles a θ)).det := by
  exact (determinant_restrict_sum_hyperplane _
    (fullAngularJacobian_column_sum τ lam p m (signedAngles a θ))).symm

end
end IsingBulk.HT22.Geometry
