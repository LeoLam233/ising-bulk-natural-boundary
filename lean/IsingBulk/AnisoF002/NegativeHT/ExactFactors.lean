import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# F002 negative HT: exact factors and integer derivative-order recurrence

All normalizations in the modulus of F002's first-winding model are retained.
The gamma quotient at integer order is represented by its exact factorial
quotient. This file proves the order recurrence by exact algebra, without
interpolating derivative order or differentiating an asymptotic error term.
It does not identify this model with the physical integral.
-/

namespace IsingBulk.AnisoF002.NegativeHT

open scoped BigOperators

noncomputable section

/-- The product P_n in F002. The r=0 factor is 1. -/
def factorialProduct (n : ℕ) : ℝ :=
  ∏ r ∈ Finset.range n, (Nat.factorial r : ℝ) / (2:ℝ)^r

theorem factorialProduct_pos (n : ℕ) : 0 < factorialProduct n := by
  unfold factorialProduct
  apply Finset.prod_pos
  intro r hr
  exact div_pos (by exact_mod_cast Nat.factorial_pos r) (by positivity)

theorem factorialProduct_step (n : ℕ) :
    factorialProduct (n+1) = factorialProduct n * ((Nat.factorial n : ℝ)/(2:ℝ)^n) := by
  simp only [factorialProduct, Finset.prod_range_succ]

/-- Exact natural-number representation of Gamma(j+1-a)/Gamma(j+1), for a≤j. -/
def gammaQuotient (j a : ℕ) : ℝ := (Nat.factorial (j-a) : ℝ)/(Nat.factorial j : ℝ)

theorem gammaQuotient_pos (j a : ℕ) : 0 < gammaQuotient j a := by
  exact div_pos (by exact_mod_cast Nat.factorial_pos (j-a))
    (by exact_mod_cast Nat.factorial_pos j)

theorem gammaQuotient_order_step (j a : ℕ) (ha : a ≤ j) :
    gammaQuotient (j+1) a = gammaQuotient j a * (((j+1:ℕ):ℝ)-a)/((j+1:ℕ):ℝ) := by
  have hsub : j+1-a = (j-a)+1 := by omega
  have hcast : ((j-a+1:ℕ):ℝ) = ((j+1:ℕ):ℝ) - a := by
    rw [Nat.cast_add, Nat.cast_sub ha, Nat.cast_one, Nat.cast_add, Nat.cast_one]
    ring
  unfold gammaQuotient
  rw [hsub, Nat.factorial_succ, Nat.factorial_succ]
  push_cast
  have hf : (Nat.factorial j : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  have hj : (j:ℝ)+1 ≠ 0 := by positivity
  have hcast' : (j-a:ℕ)+1 = j+1-a := by omega
  have hr : ((j-a:ℕ):ℝ)+1 = (j:ℝ)+1-a := by
    rw [Nat.cast_sub ha]
    ring
  rw [hr]
  field_simp

/-- Integer exponent alpha_n, evaluated on the odd particle subsequence in F002. -/
def particleExponent (n : ℕ) : ℕ := (n^2-1)/2

/-- On odd particle number this is the exact integral exponent, not a rounded
real exponent. -/
theorem particleExponent_odd (k : ℕ) : particleExponent (2*k+1) = 2*k*(k+1) := by
  unfold particleExponent
  have he : (2*k+1)^2 = 2*(2*k*(k+1))+1 := by ring
  rw [he, Nat.add_sub_cancel]
  omega

/-- Full positive prefactor of |M(n,j)|: powers of 2, B, n, pi, s, h and P_n.
Here B and h are their complex moduli and s=sin(phi)>0. -/
def modelPrefactor (n : ℕ) (B h s : ℝ) : ℝ :=
  (2:ℝ) ^ (2-(particleExponent n:ℝ)) *
    B ^ ((particleExponent n:ℝ)-1/2) * factorialProduct n *
    (n:ℝ) ^ ((particleExponent n:ℝ)-3/2) /
      (Real.pi ^ (((n:ℝ)-1)/2) * s^(2*particleExponent n)) *
    h ^ (-(particleExponent n:ℝ))

theorem modelPrefactor_pos (n : ℕ) (B h s : ℝ)
    (hn : 0 < n) (hB : 0 < B) (hh : 0 < h) (hs : 0 < s) :
    0 < modelPrefactor n B h s := by
  unfold modelPrefactor
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hp := factorialProduct_pos n
  positivity

/-- The complete modulus model, with all factors still present. -/
def modelMagnitude (n j : ℕ) (B h s τ : ℝ) : ℝ :=
  modelPrefactor n B h s * τ^(particleExponent n) / τ^(j+1) *
    gammaQuotient j (particleExponent n)

theorem modelMagnitude_pos (n j : ℕ) (B h s τ : ℝ)
    (hn : 0<n) (hB : 0<B) (hh : 0<h) (hs : 0<s) (hτ : 0<τ) :
    0 < modelMagnitude n j B h s τ := by
  unfold modelMagnitude
  exact mul_pos (div_pos (mul_pos (modelPrefactor_pos n B h s hn hB hh hs)
    (pow_pos hτ _)) (pow_pos hτ _)) (gammaQuotient_pos _ _)

/-- Exact one-step recurrence; all n-dependent prefactors cancel only after
forming the ratio in derivative order j. -/
theorem modelMagnitude_order_step (n j : ℕ) (B h s τ : ℝ)
    (ha : particleExponent n ≤ j) (hτ : τ ≠ 0) :
    modelMagnitude n (j+1) B h s τ = modelMagnitude n j B h s τ *
      (((j+1:ℕ):ℝ) - particleExponent n) / (τ*((j+1:ℕ):ℝ)) := by
  unfold modelMagnitude
  rw [gammaQuotient_order_step j _ ha]
  rw [show j+1+1 = (j+1)+1 by omega, pow_succ]
  field_simp

/-- Logarithmic version of the exact integer-order recurrence. -/
theorem log_modelMagnitude_order_step (n j : ℕ) (B h s τ : ℝ)
    (hn : 0<n) (hB : 0<B) (hh : 0<h) (hs : 0<s) (hτ : 0<τ)
    (ha : particleExponent n ≤ j) :
    Real.log (modelMagnitude n (j+1) B h s τ) -
      Real.log (modelMagnitude n j B h s τ) =
        Real.log (((j+1:ℕ):ℝ) - particleExponent n) -
        Real.log τ - Real.log ((j+1:ℕ):ℝ) := by
  have hm := modelMagnitude_pos n j B h s τ hn hB hh hs hτ
  have hj : (0:ℝ) < ((j+1:ℕ):ℝ) := by positivity
  have hja : (0:ℝ) < ((j+1:ℕ):ℝ) - particleExponent n := by
    have : particleExponent n < j+1 := by omega
    exact sub_pos.mpr (by exact_mod_cast this)
  rw [modelMagnitude_order_step n j B h s τ ha hτ.ne']
  rw [Real.log_div (mul_ne_zero hm.ne' hja.ne') (mul_ne_zero hτ.ne' hj.ne')]
  rw [Real.log_mul hm.ne' hja.ne', Real.log_mul hτ.ne' hj.ne']
  ring

/-- Exact neighboring-particle comparison recurrence in F002. It retains
arbitrary distinct complex-modulus prefactors on the two particle sectors. -/
theorem centered_log_ratio_order_step
    (l r j : ℕ) (Bl hl sl τl Br hr sr τr : ℝ)
    (hln : 0<l) (hlB : 0<Bl) (hlh : 0<hl) (hls : 0<sl) (hlτ : 0<τl)
    (hrn : 0<r) (hrB : 0<Br) (hrh : 0<hr) (hrs : 0<sr) (hrτ : 0<τr)
    (hla : particleExponent l ≤ j) (hra : particleExponent r ≤ j) :
    (Real.log (modelMagnitude r (j+1) Br hr sr τr) -
       Real.log (modelMagnitude l (j+1) Bl hl sl τl)) -
    (Real.log (modelMagnitude r j Br hr sr τr) -
       Real.log (modelMagnitude l j Bl hl sl τl)) =
      Real.log (τl/τr) +
      Real.log ((((j+1:ℕ):ℝ)-particleExponent r) /
        (((j+1:ℕ):ℝ)-particleExponent l)) := by
  have hL := log_modelMagnitude_order_step l j Bl hl sl τl hln hlB hlh hls hlτ hla
  have hR := log_modelMagnitude_order_step r j Br hr sr τr hrn hrB hrh hrs hrτ hra
  have hpL : (0:ℝ) < ((j+1:ℕ):ℝ)-particleExponent l := by
    have : particleExponent l < j+1 := by omega
    exact sub_pos.mpr (by exact_mod_cast this)
  have hpR : (0:ℝ) < ((j+1:ℕ):ℝ)-particleExponent r := by
    have : particleExponent r < j+1 := by omega
    exact sub_pos.mpr (by exact_mod_cast this)
  rw [Real.log_div hlτ.ne' hrτ.ne', Real.log_div hpR.ne' hpL.ne']
  linarith

end

end IsingBulk.AnisoF002.NegativeHT
