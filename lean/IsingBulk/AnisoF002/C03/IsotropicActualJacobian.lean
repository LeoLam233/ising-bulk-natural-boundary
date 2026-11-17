import IsingBulk.AnisoF002.C03.IsotropicRightHomotopy
import IsingBulk.AnisoF002.Isotropic.BalancedDeterminant
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Actual bump derivative bounds, Jacobian, and nonzero complex variance

The smooth periodic bumps supply their own global derivative and
Lipschitz constants. Consequently the checked balanced Jacobian and
bilinear variance estimates apply to the actual full population-dependent
homotopy, with one smallness choice before every particle number.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators
open Set Metric

theorem periodic_deriv_F002 (f : ℝ → ℝ) (c : ℝ) (hp : Function.Periodic f c) :
    Function.Periodic (deriv f) c := by
  intro x
  have he : (fun y => f (y + c)) = f := funext hp
  rw [← deriv_comp_add_const f c x, he]

theorem periodic_C1_deriv_bound_F002 (f : ℝ → ℝ) (c : ℝ) (hc : c ≠ 0)
    (hp : Function.Periodic f c) (hf : ContDiff ℝ 1 f) :
    ∃ L : ℝ, 0 < L ∧ (∀ x, |deriv f x| ≤ L) ∧
      ∀ x y, |f x - f y| ≤ L * |x - y| := by
  have hk := (periodic_deriv_F002 f c hp).compact_of_continuous hc hf.continuous_deriv_one
  obtain ⟨C, hC⟩ := hk.exists_bound_of_continuousOn (f := id) continuousOn_id
  let L := max 1 C
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hbound : ∀ x, |deriv f x| ≤ L := by
    intro x
    have h := hC (deriv f x) (mem_range_self x)
    have h' : |deriv f x| ≤ C := by simpa only [id_eq, Real.norm_eq_abs] using h
    exact h'.trans (le_max_right _ _)
  refine ⟨L, hL, hbound, ?_⟩
  intro x y
  have hm := Convex.norm_image_sub_le_of_norm_deriv_le
    (f := f) (s := univ) (fun x _ => hf.differentiable_one x)
    (fun x _ => by simpa only [Real.norm_eq_abs] using hbound x) convex_univ
    (show y ∈ (univ : Set ℝ) from mem_univ y) (show x ∈ (univ : Set ℝ) from mem_univ x)
  simpa only [Real.norm_eq_abs] using hm

theorem actual_bump_global_first_bounds (η : ℝ) :
    ∃ L : ℝ, 0 < L ∧
      (∀ x, |deriv (upperPeriodicBump η) x| ≤ L) ∧
      (∀ x, |deriv (lowerPeriodicBump η) x| ≤ L) ∧
      (∀ x y, |upperPeriodicBump η x - upperPeriodicBump η y| ≤ L * |x - y|) ∧
      (∀ x y, |lowerPeriodicBump η x - lowerPeriodicBump η y| ≤ L * |x - y|) := by
  have hc : 2 * Real.pi ≠ 0 := ne_of_gt (mul_pos (by norm_num) Real.pi_pos)
  obtain ⟨Lp, hLp, hpD, hpL⟩ := periodic_C1_deriv_bound_F002 (upperPeriodicBump η) _ hc
    (upperPeriodicBump_periodic η) (upperPeriodicBump_contDiff η)
  obtain ⟨Lm, _, hmD, hmL⟩ := periodic_C1_deriv_bound_F002 (lowerPeriodicBump η) _ hc
    (lowerPeriodicBump_periodic η) (lowerPeriodicBump_contDiff η)
  refine ⟨max Lp Lm, hLp.trans_le (le_max_left _ _),
    fun x => (hpD x).trans (le_max_left _ _), fun x => (hmD x).trans (le_max_right _ _), ?_, ?_⟩
  · intro x y
    exact (hpL x y).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
  · intro x y
    exact (hmL x y).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (abs_nonneg _))

def actualBalancedJacobian {ι : Type*} [Fintype ι] (η τ ξ : ℝ) (θ : ι → ℝ) :
    (ι → ℂ) →ₗ[ℂ] (ι → ℂ) :=
  balancedAngularJacobian ((ξ * τ) / Fintype.card ι)
    (fun i => upperPeriodicBump η (θ i)) (fun i => lowerPeriodicBump η (θ i))
    (fun i => deriv (upperPeriodicBump η) (θ i))
    (fun i => deriv (lowerPeriodicBump η) (θ i))

/-- The actual full Jacobian is an automorphism and the actual complex
variance is nonzero away from complete equality. The constants precede N. -/
theorem exists_actual_balanced_uniform_regularity (η : ℝ) :
    ∃ δ L : ℝ, 0 < δ ∧ 0 < L ∧
      ∀ (N : ℕ), 0 < N →
      ∀ τ ∈ Icc 0 δ, ∀ ξ ∈ Icc 0 1, ∀ θ : Fin N → ℝ,
        Function.Bijective (actualBalancedJacobian η τ ξ θ) ∧
          (∀ a b, actualBalancedJacobian η τ ξ θ a = b → ‖a‖ ≤ 2 * ‖b‖) ∧
          ∀ i j, θ i ≠ θ j → pairVariance (actualHomotopyAngle η τ ξ θ) ≠ 0 := by
  obtain ⟨L, hL, hpD, hmD, hpL, hmL⟩ := actual_bump_global_first_bounds η
  let δ := 1 / (8 * L)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδL : δ * L = 1 / 8 := by dsimp [δ]; field_simp
  refine ⟨δ, L, hδ, hL, ?_⟩
  intro N hN τ hτ ξ hξ θ
  have hs : 0 ≤ ξ * τ := mul_nonneg hξ.1 hτ.1
  have hsL : (ξ * τ) * L ≤ 1 / 8 := by
    have hξτ : ξ * τ ≤ τ := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hξ.2 hτ.1
    exact (mul_le_mul_of_nonneg_right (hξτ.trans hτ.2) hL.le).trans_eq hδL
  have hsmall : 4 * (ξ * τ) * L < 1 := by linarith
  have hsq : ((ξ * τ) * (L + L)) ^ 2 < 1 := by
    have hnonneg : 0 ≤ (ξ * τ) * L := mul_nonneg hs hL.le
    nlinarith
  have hcard : 0 < Fintype.card (Fin N) := by simpa using hN
  have hbij := balancedAngularJacobian_bijective
    (fun i => upperPeriodicBump η (θ i)) (fun i => lowerPeriodicBump η (θ i))
    (fun i => deriv (upperPeriodicBump η) (θ i))
    (fun i => deriv (lowerPeriodicBump η) (θ i)) (ξ * τ) L hcard hs hL.le
    (fun i => upperPeriodicBump_bounds η (θ i)) (fun i => lowerPeriodicBump_bounds η (θ i))
    (fun i => hpD (θ i)) (fun i => hmD (θ i)) hsmall
  refine ⟨hbij, ?_, ?_⟩
  · intro a b hab
    have hb := balancedAngularJacobian_inverse_bound
      (fun i => upperPeriodicBump η (θ i)) (fun i => lowerPeriodicBump η (θ i))
      (fun i => deriv (upperPeriodicBump η) (θ i))
      (fun i => deriv (lowerPeriodicBump η) (θ i)) a b (ξ * τ) L hcard hs hL.le
      (fun i => upperPeriodicBump_bounds η (θ i)) (fun i => lowerPeriodicBump_bounds η (θ i))
      (fun i => hpD (θ i)) (fun i => hmD (θ i)) hsmall hab
    have hle : ‖b‖ / (1 - 4 * (ξ * τ) * L) ≤ 2 * ‖b‖ := by
      apply (div_le_iff₀ (sub_pos.mpr hsmall)).mpr
      nlinarith [norm_nonneg b]
    exact hb.trans hle
  · intro i j hij
    have hv := balancedContour_variance_ne_zero θ
      (fun k => upperPeriodicBump η (θ k)) (fun k => lowerPeriodicBump η (θ k))
      (ξ * τ) L L hcard hs hL.le hL.le
      (fun k => upperPeriodicBump_bounds η (θ k)) (fun k => lowerPeriodicBump_bounds η (θ k))
      (fun k l => hpL (θ k) (θ l)) (fun k l => hmL (θ k) (θ l)) hsq i j hij
    have he : ξ * (τ / (Fintype.card (Fin N) : ℝ)) = (ξ * τ) / Fintype.card (Fin N) := by ring
    change pairVariance
      (contourCoordinate θ (balancedShift (ξ * (τ / Fintype.card (Fin N)))
        (fun k => upperPeriodicBump η (θ k)) (fun k => lowerPeriodicBump η (θ k)))) ≠ 0
    rw [he]
    exact hv

end IsingBulk.AnisoF002.Isotropic
