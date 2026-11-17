import IsingBulk.AnisoF002.Isotropic.BalancedJacobian
import Mathlib.LinearAlgebra.Determinant

/-!
# Full and constrained determinants of the actual balanced Jacobian

Frozen F002 §7.3.1 identifies the ambient determinant of `M = I - i Dh`
with its determinant on the constrained angular hyperplane.  The proof
here uses the actual complete population-dependent map.  Its action on
the quotient by the zero-sum space is exactly the identity.

This is a determinant identity, not a claim that the physical contour
integral or its measure transformation has already been formalized.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- Tangent space to either signed total-angle constraint. -/
def zeroSumAngles : Submodule ℂ (ι → ℂ) where
  carrier := {a | ∑ i, a i = 0}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    change (∑ i, (a i + b i)) = 0
    rw [Finset.sum_add_distrib, ha, hb, add_zero]
  smul_mem' := by
    intro c a ha
    change (∑ i, c * a i) = 0
    rw [← Finset.mul_sum, ha, mul_zero]

/-- The full Jacobian preserves the actual constrained tangent space. -/
theorem balancedAngularJacobian_preserves_zeroSum
    (scale : ℝ) (p m dp dm : ι → ℝ) :
    zeroSumAngles ≤ (zeroSumAngles : Submodule ℂ (ι → ℂ)).comap
      (balancedAngularJacobian scale p m dp dm) := by
  intro a ha
  change (∑ i, balancedAngularJacobian scale p m dp dm a i) = 0
  rw [sum_balancedAngularJacobian]
  exact ha

/-- On the normal quotient the full Jacobian is exactly the identity. -/
theorem balancedAngularJacobian_quotient_eq_id
    (scale : ℝ) (p m dp dm : ι → ℝ) :
    (zeroSumAngles : Submodule ℂ (ι → ℂ)).mapQ zeroSumAngles
      (balancedAngularJacobian scale p m dp dm)
      (balancedAngularJacobian_preserves_zeroSum scale p m dp dm) = LinearMap.id := by
  apply LinearMap.ext
  intro q
  refine Submodule.Quotient.induction_on _ q ?_
  intro a
  rw [Submodule.mapQ_apply, LinearMap.id_apply]
  apply (Submodule.Quotient.eq _).2
  change (∑ i, (balancedAngularJacobian scale p m dp dm a i - a i)) = 0
  rw [Finset.sum_sub_distrib, sum_balancedAngularJacobian, sub_self]

/-- The ambient determinant is precisely the tangent determinant, with no
extra normal-direction factor.  No invertibility hypothesis is needed. -/
theorem balancedAngularJacobian_det_eq_tangent_det
    (scale : ℝ) (p m dp dm : ι → ℝ) :
    (balancedAngularJacobian scale p m dp dm).det =
      ((balancedAngularJacobian scale p m dp dm).restrict
        (balancedAngularJacobian_preserves_zeroSum scale p m dp dm)).det := by
  have h := LinearMap.det_eq_det_mul_det
    (zeroSumAngles : Submodule ℂ (ι → ℂ))
    (balancedAngularJacobian scale p m dp dm)
    (balancedAngularJacobian_preserves_zeroSum scale p m dp dm)
  rw [balancedAngularJacobian_quotient_eq_id, LinearMap.det_id, mul_one] at h
  exact h

/-- At the same fixed small deformation size the actual determinant is
nonzero for every particle number. -/
theorem balancedAngularJacobian_det_ne_zero
    (p m dp dm : ι → ℝ) (τ L : ℝ)
    (hn : 0 < Fintype.card ι) (hτ : 0 ≤ τ) (hL : 0 ≤ L)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (hm : ∀ i, 0 ≤ m i ∧ m i ≤ 1)
    (hdp : ∀ i, |dp i| ≤ L) (hdm : ∀ i, |dm i| ≤ L)
    (hsmall : 4 * τ * L < 1) :
    (balancedAngularJacobian (τ / Fintype.card ι) p m dp dm).det ≠ 0 := by
  intro hz
  have hk := LinearMap.det_eq_zero_iff_ker_ne_bot.mp hz
  apply hk
  exact LinearMap.ker_eq_bot.mpr
    (balancedAngularJacobian_injective p m dp dm τ L hn hτ hL hp hm hdp hdm hsmall)

end IsingBulk.AnisoF002.Isotropic
