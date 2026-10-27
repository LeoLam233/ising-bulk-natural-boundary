import Mathlib.Tactic
import Mathlib.Basic.Complex.BigOperators
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Add
import IsingBulk.Tail.SelectorPiola
import IsingBulk.Preferred22.Coordinates
import IsingBulk.Preferred22.Contour
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Algebra.Order.ToIntervalMod

/-!
# LT22 Preferred: the exact collective transport algebra

This file implements the finite-dimensional identities in (7.10),
(7.12), and (7.13).  It does not assume a tail theorem.  The analytic
construction of the inverse chart, its divided-difference margin, and
the differentiated estimates remain separate obligations.
-/

namespace IsingBulk.Preferred22
noncomputable section
open scoped BigOperators

section Collective
variable {ι : Type*} [Fintype ι]

/-- The pair quotient in (7.12), including its zero value on the diagonal. -/
def collectivePair (u v : ι → ℂ) (i j : ι) : ℂ :=
  (u i - u j)^2 / (v i - v j)

/-- A symmetric formula for `∑ i < j, (u i-u j)^2`. -/
def collectiveDenominator (u : ι → ℂ) : ℂ :=
  (∑ i, ∑ j, (u i-u j)^2) / 2

/-- The manuscript's literal sum over `i < j`. -/
def upperPairSum [LinearOrder ι] (u : ι → ℂ) : ℂ :=
  ∑ i, ∑ j, if i < j then (u i-u j)^2 else 0

theorem collectiveDenominator_eq_upper [LinearOrder ι] (u : ι → ℂ) :
    collectiveDenominator u = upperPairSum u := by
  have hpoint (i j : ι) : (u i-u j)^2 =
      (if i < j then (u i-u j)^2 else 0) +
      (if j < i then (u i-u j)^2 else 0) := by
    rcases lt_trichotomy i j with hij | hij | hij
    · simp [hij, not_lt.mpr (le_of_lt hij)]
    · subst j; simp
    · simp [hij, not_lt.mpr (le_of_lt hij)]
  have hswap : (∑ i, ∑ j, if j < i then (u i-u j)^2 else 0) = upperPairSum u := by
    rw [Finset.sum_comm]
    unfold upperPairSum
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> ring
  have hsum : (∑ i, ∑ j, (u i-u j)^2) = upperPairSum u+upperPairSum u := by
    conv_lhs => arg 2; ext i; arg 2; ext j; rw [hpoint i j]
    simp only [Finset.sum_add_distrib]
    rw [hswap]
    rfl
  unfold collectiveDenominator
  rw [hsum]
  ring

def collectiveResidual (uDot v : ι → ℂ) (c₀ : ℂ) : ℂ :=
  -(∑ i, uDot i) - c₀ * ∑ i, v i

/-- The actual algebraic formula (7.12), not an existential solution. -/
def collectiveField (u uDot v : ι → ℂ) (c₀ : ℂ) (i : ι) : ℂ :=
  c₀ + collectiveResidual uDot v c₀ / collectiveDenominator u *
    ∑ j, collectivePair u v i j

omit [Fintype ι] in
theorem collectivePair_self (u v : ι → ℂ) (i : ι) :
    collectivePair u v i i = 0 := by
  simp [collectivePair]

omit [Fintype ι] in
theorem collectivePair_swap (u v : ι → ℂ) (i j : ι) :
    collectivePair u v j i = -collectivePair u v i j := by
  unfold collectivePair
  rw [show u j-u i = -(u i-u j) by ring,
    show v j-v i = -(v i-v j) by ring]
  simp only [neg_sq, div_neg]

theorem collectivePair_total (u v : ι → ℂ) :
    (∑ i, ∑ j, collectivePair u v i j) = 0 := by
  have h : (∑ i, ∑ j, collectivePair u v i j) =
      -(∑ i, ∑ j, collectivePair u v i j) := by
    calc
      _ = ∑ j, ∑ i, collectivePair u v i j := Finset.sum_comm
      _ = ∑ j, ∑ i, -collectivePair u v j i := by
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro i _
        exact collectivePair_swap u v j i
      _ = _ := by simp
  linear_combination h / 2

/- The slope-collision hypothesis is exactly what regular divided differences
provide.  It prevents totalized division from hiding a nonzero numerator. -/
omit [Fintype ι] in
theorem collectivePair_weighted (u v : ι → ℂ)
    (hcollision : ∀ i j, v i = v j → u i = u j) (i j : ι) :
    v i * collectivePair u v i j + v j * collectivePair u v j i =
      (u i-u j)^2 := by
  rw [collectivePair_swap]
  by_cases hv : v i = v j
  · simp [collectivePair, hv, hcollision i j hv]
  · have hne : v i-v j ≠ 0 := sub_ne_zero.mpr hv
    unfold collectivePair
    field_simp
    ring

theorem collectivePair_weighted_total (u v : ι → ℂ)
    (hcollision : ∀ i j, v i = v j → u i = u j) :
    (∑ i, v i * ∑ j, collectivePair u v i j) =
      collectiveDenominator u := by
  have hpair := fun i j => collectivePair_weighted u v hcollision i j
  have hsum :
      (∑ i, ∑ j, (v i * collectivePair u v i j +
        v j * collectivePair u v j i)) =
        ∑ i, ∑ j, (u i-u j)^2 := by
    apply Finset.sum_congr rfl
    intro i _
    exact Finset.sum_congr rfl (fun j _ => hpair i j)
  simp only [Finset.sum_add_distrib] at hsum
  have hswap : (∑ i, ∑ j, v j * collectivePair u v j i) =
      ∑ i, ∑ j, v i * collectivePair u v i j := by
    rw [Finset.sum_comm]
  rw [hswap] at hsum
  unfold collectiveDenominator
  simp only [Finset.mul_sum]
  linear_combination hsum / 2

/-- First identity in (7.13): the complete phase is frozen. -/
theorem collectiveField_sum (u uDot v : ι → ℂ) (c₀ : ℂ) :
    (∑ i, collectiveField u uDot v c₀ i) = Fintype.card ι * c₀ := by
  simp only [collectiveField, Finset.sum_add_distrib, ← Finset.mul_sum,
    collectivePair_total, mul_zero, add_zero, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]

/-- Second identity in (7.13): the angular constraint is frozen. -/
theorem collectiveField_weighted_sum (u uDot v : ι → ℂ) (c₀ : ℂ)
    (hcollision : ∀ i j, v i = v j → u i = u j)
    (hR : collectiveDenominator u ≠ 0) :
    (∑ i, v i * collectiveField u uDot v c₀ i) = -(∑ i, uDot i) := by
  calc
    _ = c₀ * (∑ i, v i) +
        collectiveResidual uDot v c₀ / collectiveDenominator u *
          (∑ i, v i * ∑ j, collectivePair u v i j) := by
      simp only [collectiveField, mul_add, Finset.sum_add_distrib,
        Finset.mul_sum]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring
    _ = c₀ * (∑ i, v i) + collectiveResidual uDot v c₀ := by
      rw [collectivePair_weighted_total u v hcollision, div_mul_cancel₀ _ hR]
    _ = _ := by unfold collectiveResidual; ring

/-- Named-anchor field (7.10). -/
def anchorField [DecidableEq ι] (uDot v : ι → ℂ) (a : ι) (i : ι) : ℂ :=
  if i = a then -(∑ j, uDot j) / v a else 0

theorem anchorField_weighted_sum [DecidableEq ι] (uDot v : ι → ℂ) (a : ι)
    (ha : v a ≠ 0) :
    (∑ i, v i * anchorField uDot v a i) = -(∑ i, uDot i) := by
  simp only [anchorField, mul_ite, mul_zero]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  field_simp

end Collective

section Center
variable {ι : Type*} [Fintype ι]

/-- The moving-center phase `φ=q-U+w_B`. -/
def movingPhase (u q : ℂ) (wB : ℂ) : ℂ := q-u+wB

theorem movingPhase_sum (u q : ι → ℂ) (wB : ℂ) :
    (∑ i, movingPhase (u i) (q i) wB) =
      (∑ i, q i) - (∑ i, u i) + Fintype.card ι * wB := by
  simp [movingPhase, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    nsmul_eq_mul]

/-- Tangency and the moving-center correction imply exact phase freezing. -/
theorem movingPhase_transport_zero (uDot v B : ι → ℂ) (wB' : ℂ)
    (hangle : (∑ i, v i*B i) = -(∑ i, uDot i))
    (hphase : (∑ i, B i) = -(Fintype.card ι:ℂ)*wB') :
    (∑ i, ((1-v i)*B i-uDot i+wB')) = 0 := by
  simp only [sub_mul, one_mul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  rw [hangle, hphase]
  ring

end Center

section Geometry
variable {ι : Type*} [Fintype ι]

def realPairEnergy (θ : ι → ℝ) : ℝ :=
  (∑ i, ∑ j, (θ i-θ j)^2)/2

def displacedAngles (θ h : ι → ℝ) (i : ι) : ℂ :=
  (θ i:ℂ) - Complex.I*(h i:ℂ)

/-- The real part in (7.15) is an exact identity on the actual contour. -/
theorem collectiveDenominator_realpart (θ h : ι → ℝ) :
    (collectiveDenominator (displacedAngles θ h)).re =
      realPairEnergy θ-realPairEnergy h := by
  have hp (i j : ι) :
      ((displacedAngles θ h i-displacedAngles θ h j)^2).re =
        (θ i-θ j)^2-(h i-h j)^2 := by
    simp [displacedAngles, pow_two, Complex.mul_re, Complex.mul_im]
    ring
  simp only [collectiveDenominator, Complex.div_ofNat_re, Complex.re_sum,
    hp, Finset.sum_sub_distrib, realPairEnergy]
  ring

theorem realPairEnergy_nonneg (θ : ι → ℝ) : 0 ≤ realPairEnergy θ := by
  unfold realPairEnergy
  positivity

theorem realPairEnergy_pos (θ : ι → ℝ) (i j : ι) (hij : θ i ≠ θ j) :
    0 < realPairEnergy θ := by
  unfold realPairEnergy
  apply div_pos _ (by norm_num)
  apply Finset.sum_pos'
  · intro a _
    exact Finset.sum_nonneg (fun b _ => sq_nonneg (θ a-θ b))
  · refine ⟨i, Finset.mem_univ _, ?_⟩
    apply Finset.sum_pos'
    · intro b _
      exact sq_nonneg (θ i-θ b)
    · exact ⟨j, Finset.mem_univ _, sq_pos_of_ne_zero (sub_ne_zero.mpr hij)⟩

theorem realPairEnergy_displacement_bound (θ h : ι → ℝ) (L : ℝ)
    (hL : ∀ i j, (h i-h j)^2 ≤ L^2*(θ i-θ j)^2) :
    realPairEnergy h ≤ L^2*realPairEnergy θ := by
  unfold realPairEnergy
  have hs : (∑ i, ∑ j, (h i-h j)^2) ≤
      ∑ i, ∑ j, L^2*(θ i-θ j)^2 := by
    exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hL i j))
  simp only [← Finset.mul_sum] at hs
  nlinarith

/-- Uniform noncancellation of the complex denominator, with the exact
small-displacement hypothesis used in (7.15). -/
theorem collectiveDenominator_ne_zero (θ h : ι → ℝ) (L : ℝ)
    (hLsmall : L^2 < 1)
    (hL : ∀ i j, (h i-h j)^2 ≤ L^2*(θ i-θ j)^2)
    (i j : ι) (hij : θ i ≠ θ j) :
    collectiveDenominator (displacedAngles θ h) ≠ 0 := by
  have hp := realPairEnergy_pos θ i j hij
  have hb := realPairEnergy_displacement_bound θ h L hL
  have hr : 0 < (collectiveDenominator (displacedAngles θ h)).re := by
    rw [collectiveDenominator_realpart]
    nlinarith
  intro hz
  rw [hz, Complex.zero_re] at hr
  exact (lt_irrefl 0) hr

/-- A single actual pair gives a particle-independent diameter lower bound. -/
theorem realPairEnergy_ge_half_pair (θ : ι → ℝ) (i j : ι) :
    (θ i-θ j)^2/2 ≤ realPairEnergy θ := by
  have hrow : (θ i-θ j)^2 ≤ ∑ b, (θ i-θ b)^2 :=
    Finset.single_le_sum (fun b _ => sq_nonneg (θ i-θ b)) (Finset.mem_univ j)
  have hsum : (∑ b, (θ i-θ b)^2) ≤ ∑ a, ∑ b, (θ a-θ b)^2 :=
    Finset.single_le_sum (fun a _ => Finset.sum_nonneg (fun b _ => sq_nonneg (θ a-θ b)))
      (Finset.mem_univ i)
  unfold realPairEnergy
  linarith

/-- Quantitative source denominator bound in (7.15), uniform in particle
count and containing no inverse temperature-distance factor. -/
theorem collectiveDenominator_norm_lower (θ h : ι → ℝ) (L : ℝ)
    (hLsmall : L^2 < 1)
    (hL : ∀ i j, (h i-h j)^2 ≤ L^2*(θ i-θ j)^2) (i j : ι) :
    ((1-L^2)/2)*(θ i-θ j)^2 ≤ ‖collectiveDenominator (displacedAngles θ h)‖ := by
  have hp := realPairEnergy_ge_half_pair θ i j
  have hb := realPairEnergy_displacement_bound θ h L hL
  have henergy : (1-L^2)*realPairEnergy θ ≤
      (collectiveDenominator (displacedAngles θ h)).re := by
    rw [collectiveDenominator_realpart]
    linarith
  have hlo := mul_le_mul_of_nonneg_left hp (by linarith : 0 ≤ 1-L^2)
  exact (by nlinarith : ((1-L^2)/2)*(θ i-θ j)^2 ≤
    (collectiveDenominator (displacedAngles θ h)).re).trans (Complex.re_le_norm _)

omit [Fintype ι] in
theorem displacedAngles_norm_sq (θ h : ι → ℝ) (i j : ι) :
    ‖displacedAngles θ h i-displacedAngles θ h j‖^2 =
      (θ i-θ j)^2+(h i-h j)^2 := by
  rw [Complex.sq_norm,Complex.normSq_apply]
  simp [displacedAngles,Complex.mul_re,Complex.mul_im]
  ring

/-- The complete pair square sum is controlled by the same noncancelling
R; this is the second quantitative assertion following (7.15). -/
theorem collectiveDenominator_pair_norm_control (θ h : ι → ℝ) (L : ℝ)
    (hLsmall : L^2 < 1)
    (hL : ∀ i j, (h i-h j)^2 ≤ L^2*(θ i-θ j)^2) :
    (1-L^2)*(∑ i, ∑ j, ‖displacedAngles θ h i-displacedAngles θ h j‖^2) ≤
      2*(1+L^2)*‖collectiveDenominator (displacedAngles θ h)‖ := by
  have he : (∑ i, ∑ j, ‖displacedAngles θ h i-displacedAngles θ h j‖^2) =
      2*(realPairEnergy θ+realPairEnergy h) := by
    simp only [displacedAngles_norm_sq,Finset.sum_add_distrib,realPairEnergy]
    ring
  have hb := realPairEnergy_displacement_bound θ h L hL
  have hR : (1-L^2)*realPairEnergy θ ≤ ‖collectiveDenominator (displacedAngles θ h)‖ := by
    have hr := Complex.re_le_norm (collectiveDenominator (displacedAngles θ h))
    rw [collectiveDenominator_realpart] at hr
    linarith
  rw [he]
  have hmul := mul_le_mul_of_nonneg_left hb (by linarith : 0 ≤ 1-L^2)
  have hmul' := mul_le_mul_of_nonneg_left hR (by positivity : 0 ≤ 2*(1+L^2))
  nlinarith

/-- Equations (7.7) and (7.8) for the actual collective formula, with its
denominator discharged by (7.15), rather than postulated nonzero. -/
theorem actual_collective_constraints (θ h : ι → ℝ) (uDot v : ι → ℂ)
    (wB' : ℂ) (L : ℝ)
    (hLsmall : L^2 < 1)
    (hL : ∀ i j, (h i-h j)^2 ≤ L^2*(θ i-θ j)^2)
    (i j : ι) (hij : θ i ≠ θ j)
    (hcollision : ∀ a b, v a = v b → displacedAngles θ h a = displacedAngles θ h b) :
    (∑ a, collectiveField (displacedAngles θ h) uDot v (-wB') a) =
      -(Fintype.card ι:ℂ)*wB' ∧
    (∑ a, v a*collectiveField (displacedAngles θ h) uDot v (-wB') a) =
      -(∑ a, uDot a) := by
  constructor
  · rw [collectiveField_sum]
    ring
  · exact collectiveField_weighted_sum _ _ _ _ hcollision
      (collectiveDenominator_ne_zero θ h L hLsmall hL i j hij)

theorem preferred_sum_mulVec {N : ℕ} (M : Matrix (Fin N) (Fin N) ℂ)
    (hcol : ∀ j, (∑ i, M i j) = 1) (x : Fin N → ℂ) :
    (∑ i, (M.mulVec x) i) = ∑ i, x i := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul, hcol, one_mul]

/-- The exact inverse Jacobian preserves the sum functional. -/
theorem preferred_sum_inverse_mulVec {N : ℕ} (M : Matrix (Fin N) (Fin N) ℂ)
    (hcol : ∀ j, (∑ i, M i j) = 1) (hdet : M.det ≠ 0) (x : Fin N → ℂ) :
    (∑ i, (M⁻¹.mulVec x) i) = ∑ i, x i := by
  have hm : M.mulVec (M⁻¹.mulVec x) = x := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet),
      Matrix.one_mulVec]
  have hs := congrArg (fun y : Fin N → ℂ => ∑ i, y i) hm
  rw [preferred_sum_mulVec M hcol] at hs
  exact hs

def preferredAngularRepresentative {N : ℕ} (M : Matrix (Fin N) (Fin N) ℂ)
    (uDot uQ B : Fin N → ℂ) (i : Fin N) : ℂ :=
  -(M⁻¹.mulVec (fun j => uDot j+uQ j*B j)) i

/-- Formula (7.6) is tangent when the residual constraint (7.7) holds. -/
theorem preferredAngularRepresentative_tangent {N : ℕ}
    (M : Matrix (Fin N) (Fin N) ℂ) (uDot uQ B : Fin N → ℂ)
    (hcol : ∀ j, (∑ i, M i j) = 1) (hdet : M.det ≠ 0)
    (hconstraint : (∑ i, uQ i*B i) = -(∑ i, uDot i)) :
    (∑ i, preferredAngularRepresentative M uDot uQ B i) = 0 := by
  simp only [preferredAngularRepresentative, Finset.sum_neg_distrib]
  rw [preferred_sum_inverse_mulVec M hcol hdet, Finset.sum_add_distrib, hconstraint]
  ring

end Geometry

section ScalarTransport
open IsingBulk.Tail
open scoped Topology

/-- Cramer's rule identifies the cofactor flux with `J V`. -/
theorem preferred_cofactor_flux {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ)
    (v : Fin N → ℂ) (hA : A.det ≠ 0) (i : Fin N) :
    (A.updateCol i v).det = A.det*(A⁻¹.mulVec v) i := by
  have h := congrFun (Matrix.det_smul_inv_mulVec_eq_cramer A v
    (isUnit_iff_ne_zero.mpr hA)) i
  simpa only [Pi.smul_apply, smul_eq_mul, Matrix.cramer_apply] using h.symm

/-- The source angular derivative matrix becomes the exact regular-coordinate
divergence through `trace(A⁻¹ Q)`. -/
theorem preferred_cofactor_divergence {N : ℕ} (A Q : Matrix (Fin N) (Fin N) ℂ)
    (hA : A.det ≠ 0) :
    (∑ i, (A.updateCol i (fun k => Q k i)).det) =
      A.det*Matrix.trace (A⁻¹*Q) := by
  simp_rw [preferred_cofactor_flux A _ hA]
  rw [← Finset.mul_sum]
  rfl

theorem preferred_det_updateCol_sub {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ)
    (i : Fin N) (u v : Fin N → ℂ) :
    (A.updateCol i (u-v)).det = (A.updateCol i u).det-(A.updateCol i v).det := by
  change A.cramer (u-v) i = A.cramer u i-A.cramer v i
  rw [map_sub]
  rfl

/-- Pointwise scalar transport in cofactor form. All derivatives here are
actual real derivatives on the original angular domain. The hypotheses are
the chain and mixed-derivative data of the coordinate map, rather than an
assumed transport identity. -/
theorem preferred_scalar_transport_cofactor {N : ℕ}
    (G : ℝ → (Fin N → ℝ) → ℂ)
    (A : ℝ → (Fin N → ℝ) → Matrix (Fin N) (Fin N) ℂ)
    (v : (Fin N → ℝ) → Fin N → ℂ) (t : ℝ) (θ : Fin N → ℝ)
    (L : (Fin N → ℂ) →ₗ[ℂ] ℂ) (fₛ : ℂ) (a b : Fin N → ℂ)
    (P Q : Matrix (Fin N) (Fin N) ℂ)
    (H : Fin N → Fin N → Fin N → ℂ) (hH : ∀ i j, H i j=H j i)
    (hv : v θ=a-b)
    (hGt : HasDerivAt (fun u => G u θ) (fₛ+L a) t)
    (hGx : ∀ i, HasDerivAt (fun u => G t (Function.update θ i u))
      (L (fun j => A t θ j i)) (θ i))
    (hAt : ∀ i j, HasDerivAt (fun u => A u θ i j) (P i j) t)
    (hAx : ∀ i k j, HasDerivAt (fun u => A t (Function.update θ i u) k j)
      (H i j k) (θ i))
    (hvx : ∀ i k, HasDerivAt (fun u => v (Function.update θ i u) k)
      (P k i-Q k i) (θ i)) :
    deriv (fun u => G u θ*(A u θ).det) t -
      (∑ i, deriv (fun u => G t (Function.update θ i u)*
        ((A t (Function.update θ i u)).updateCol i
          (v (Function.update θ i u))).det) (θ i)) =
      (fₛ+L b)*(A t θ).det +
        G t θ * ∑ i, ((A t θ).updateCol i (fun k => Q k i)).det := by
  have hdet := hasDerivAt_det_columns (fun u => A u θ) P t hAt
  have hm (i : Fin N) := hasDerivAt_replacement_minor
    (fun u => A t (Function.update θ i u)) (fun k j => H i j k)
    (fun u => v (Function.update θ i u)) (fun k => P k i-Q k i) (θ i) i
    (hAx i) (hvx i)
  have hd (i : Fin N) := ((hGx i).fun_mul (hm i)).deriv
  simp only [Function.update_eq_self] at hd
  have hdiv :
      (∑ i, deriv (fun u => G t (Function.update θ i u)*
        ((A t (Function.update θ i u)).updateCol i
          (v (Function.update θ i u))).det) (θ i)) =
      L (v θ)*(A t θ).det + G t θ *
        ∑ i, ((A t θ).updateCol i (fun k => P k i-Q k i)).det := by
    simp_rw [hd]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [Finset.sum_add_distrib,
      piola_algebraic_cancellation (A t θ) (v θ) H hH, add_zero]
    rw [← cofactor_gradient_identity (A t θ) (v θ) L]
  have hsub : (∑ i, ((A t θ).updateCol i (fun k => P k i-Q k i)).det) =
      (∑ i, ((A t θ).updateCol i (fun k => P k i)).det) -
      ∑ i, ((A t θ).updateCol i (fun k => Q k i)).det := by
    simp only [show (fun k => P k _-Q k _) =
        (fun k => P k _)-(fun k => Q k _) by rfl,
      preferred_det_updateCol_sub, Finset.sum_sub_distrib]
  rw [(hGt.fun_mul hdet).deriv, hdiv, hv, map_sub, hsub]
  ring

/-- The real angular weight is differentiated as a real function. This is
the cutoff term in (7.9); no analytic extension of the cutoff occurs. -/
theorem preferred_weighted_scalar_transport_cofactor {N : ℕ}
    (ω : (Fin N → ℝ) → ℝ) (dω : Fin N → ℝ)
    (G : ℝ → (Fin N → ℝ) → ℂ)
    (A : ℝ → (Fin N → ℝ) → Matrix (Fin N) (Fin N) ℂ)
    (v : (Fin N → ℝ) → Fin N → ℂ) (t : ℝ) (θ : Fin N → ℝ)
    (L : (Fin N → ℂ) →ₗ[ℂ] ℂ) (fₛ : ℂ) (a b : Fin N → ℂ)
    (P Q : Matrix (Fin N) (Fin N) ℂ)
    (H : Fin N → Fin N → Fin N → ℂ) (hH : ∀ i j, H i j=H j i)
    (hv : v θ=a-b)
    (hω : ∀ i, HasDerivAt (fun u => ω (Function.update θ i u)) (dω i) (θ i))
    (hGt : HasDerivAt (fun u => G u θ) (fₛ+L a) t)
    (hGx : ∀ i, HasDerivAt (fun u => G t (Function.update θ i u))
      (L (fun j => A t θ j i)) (θ i))
    (hAt : ∀ i j, HasDerivAt (fun u => A u θ i j) (P i j) t)
    (hAx : ∀ i k j, HasDerivAt (fun u => A t (Function.update θ i u) k j)
      (H i j k) (θ i))
    (hvx : ∀ i k, HasDerivAt (fun u => v (Function.update θ i u) k)
      (P k i-Q k i) (θ i)) :
    deriv (fun u => (ω θ:ℂ)*(G u θ*(A u θ).det)) t -
      (∑ i, deriv (fun u => (ω (Function.update θ i u):ℂ)*
        (G t (Function.update θ i u)*
        ((A t (Function.update θ i u)).updateCol i
          (v (Function.update θ i u))).det)) (θ i)) =
      (ω θ:ℂ)*((fₛ+L b)*(A t θ).det +
        G t θ * ∑ i, ((A t θ).updateCol i (fun k => Q k i)).det) -
      ∑ i, (dω i:ℂ)*(G t θ*((A t θ).updateCol i (v θ)).det) := by
  have hdet := hasDerivAt_det_columns (fun u => A u θ) P t hAt
  have htime := ((hGt.fun_mul hdet).const_mul (ω θ:ℂ)).deriv
  have hm (i : Fin N) := hasDerivAt_replacement_minor
    (fun u => A t (Function.update θ i u)) (fun k j => H i j k)
    (fun u => v (Function.update θ i u)) (fun k => P k i-Q k i) (θ i) i
    (hAx i) (hvx i)
  have hf (i : Fin N) := (hGx i).fun_mul (hm i)
  have hspace (i : Fin N) := ((hω i).ofReal_comp.fun_mul (hf i)).deriv
  simp only [Function.update_eq_self] at hspace
  have hbase := preferred_scalar_transport_cofactor G A v t θ L fₛ a b P Q H hH
    hv hGt hGx hAt hAx hvx
  have hsp (i : Fin N) :
      deriv (fun u => (ω (Function.update θ i u):ℂ)*
        (G t (Function.update θ i u)*
        ((A t (Function.update θ i u)).updateCol i
          (v (Function.update θ i u))).det)) (θ i) =
      (dω i:ℂ)*(G t θ*((A t θ).updateCol i (v θ)).det) +
        (ω θ:ℂ)*deriv (fun u => G t (Function.update θ i u)*
          ((A t (Function.update θ i u)).updateCol i
            (v (Function.update θ i u))).det) (θ i) := by
    rw [hspace i, (hf i).deriv]
    simp only [Function.update_eq_self]
  simp_rw [hsp]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [htime]
  rw [(hGt.fun_mul hdet).deriv] at hbase
  linear_combination (ω θ:ℂ)*hbase

def preferredAngularVelocity {N : ℕ}
    (A : ℝ → (Fin N → ℝ) → Matrix (Fin N) (Fin N) ℂ)
    (v : (Fin N → ℝ) → Fin N → ℂ) (t : ℝ) (θ : Fin N → ℝ) : Fin N → ℂ :=
  (A t θ)⁻¹.mulVec (v θ)

/-- Exact scalar transport (7.9), including the actual smooth real cutoff
derivative. The residual q-divergence is represented by the Jacobian trace
`trace(A⁻¹ Q)`, equal by cyclicity to `trace(Q A⁻¹)`.

This local calculus theorem is a proof, with differentiability hypotheses
spelled out. Its application to the Preferred contour still requires the
source-specific derivative and nonvanishing hypotheses. -/
theorem preferred_weighted_scalar_transport {N : ℕ}
    (ω : (Fin N → ℝ) → ℝ) (dω : Fin N → ℝ)
    (G : ℝ → (Fin N → ℝ) → ℂ)
    (A : ℝ → (Fin N → ℝ) → Matrix (Fin N) (Fin N) ℂ)
    (v : (Fin N → ℝ) → Fin N → ℂ) (t : ℝ) (θ : Fin N → ℝ)
    (L : (Fin N → ℂ) →ₗ[ℂ] ℂ) (fₛ : ℂ) (a b : Fin N → ℂ)
    (P Q : Matrix (Fin N) (Fin N) ℂ)
    (H : Fin N → Fin N → Fin N → ℂ) (hH : ∀ i j, H i j=H j i)
    (hv : v θ=a-b)
    (hAcont : ContinuousAt (fun x => A t x) θ) (hA : (A t θ).det ≠ 0)
    (hω : ∀ i, HasDerivAt (fun u => ω (Function.update θ i u)) (dω i) (θ i))
    (hGt : HasDerivAt (fun u => G u θ) (fₛ+L a) t)
    (hGx : ∀ i, HasDerivAt (fun u => G t (Function.update θ i u))
      (L (fun j => A t θ j i)) (θ i))
    (hAt : ∀ i j, HasDerivAt (fun u => A u θ i j) (P i j) t)
    (hAx : ∀ i k j, HasDerivAt (fun u => A t (Function.update θ i u) k j)
      (H i j k) (θ i))
    (hvx : ∀ i k, HasDerivAt (fun u => v (Function.update θ i u) k)
      (P k i-Q k i) (θ i)) :
    deriv (fun u => (ω θ:ℂ)*(G u θ*(A u θ).det)) t -
      (∑ i, deriv (fun u => preferredAngularVelocity A v t (Function.update θ i u) i *
        (ω (Function.update θ i u):ℂ) *
        (A t (Function.update θ i u)).det * G t (Function.update θ i u)) (θ i)) =
      (ω θ:ℂ)*(A t θ).det*
        (fₛ+L b+Matrix.trace ((A t θ)⁻¹*Q)*G t θ) -
      (∑ i, preferredAngularVelocity A v t θ i*(dω i:ℂ))*(A t θ).det*G t θ := by
  have hbase := preferred_weighted_scalar_transport_cofactor ω dω G A v t θ L fₛ a b
    P Q H hH hv hω hGt hGx hAt hAx hvx
  have hflux (i : Fin N) :
      deriv (fun u => preferredAngularVelocity A v t (Function.update θ i u) i *
        (ω (Function.update θ i u):ℂ) *
        (A t (Function.update θ i u)).det * G t (Function.update θ i u)) (θ i) =
      deriv (fun u => (ω (Function.update θ i u):ℂ)*
        (G t (Function.update θ i u)*
        ((A t (Function.update θ i u)).updateCol i
          (v (Function.update θ i u))).det)) (θ i) := by
    have hu : Continuous (fun u : ℝ => Function.update θ i u) := by fun_prop
    have hc : ContinuousAt (fun u : ℝ => (A t (Function.update θ i u)).det) (θ i) :=
      (continuous_id.matrix_det.continuousAt.comp hAcont).comp_of_eq
        hu.continuousAt (by simp)
    have hne : ∀ᶠ u in 𝓝 (θ i), (A t (Function.update θ i u)).det ≠ 0 :=
      hc.eventually_ne (by simpa only [Function.update_eq_self] using hA)
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [hne] with u huA
    rw [preferred_cofactor_flux _ _ huA]
    unfold preferredAngularVelocity
    ring
  simp_rw [hflux]
  rw [hbase, preferred_cofactor_divergence _ _ hA]
  have hcut : (∑ i, (dω i:ℂ)*(G t θ*((A t θ).updateCol i (v θ)).det)) =
      (∑ i, preferredAngularVelocity A v t θ i*(dω i:ℂ))*(A t θ).det*G t θ := by
    simp_rw [preferred_cofactor_flux _ _ hA]
    simp only [Finset.sum_mul, preferredAngularVelocity]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hcut]
  ring

end ScalarTransport

section ConstrainedDivergence
open scoped Topology

/-- Columnwise differentiation of the actual ambient tangency condition. -/
theorem preferred_tangent_derivative_sum {N : ℕ}
    (V : (Fin N → ℝ) → Fin N → ℂ) (θ : Fin N → ℝ)
    (D : Matrix (Fin N) (Fin N) ℂ)
    (htangent : ∀ᶠ x in 𝓝 θ, (∑ i, V x i) = 0)
    (hD : ∀ i j, HasDerivAt (fun u => V (Function.update θ j u) i) (D i j) (θ j))
    (j : Fin N) : (∑ i, D i j) = 0 := by
  have hsum : HasDerivAt (fun u => ∑ i, V (Function.update θ j u) i)
      (∑ i, D i j) (θ j) := HasDerivAt.fun_sum (fun i _ => hD i j)
  have hu : Continuous (fun u : ℝ => Function.update θ j u) := by fun_prop
  have hut : Filter.Tendsto (fun u : ℝ => Function.update θ j u) (𝓝 (θ j)) (𝓝 θ) := by
    simpa only [ContinuousAt, Function.update_eq_self] using (hu.continuousAt (x := θ j))
  have hz : (fun u => ∑ i, V (Function.update θ j u) i) =ᶠ[𝓝 (θ j)] (fun _ => 0) :=
    hut.eventually htangent
  have hzero : HasDerivAt (fun u => ∑ i, V (Function.update θ j u) i) 0 (θ j) :=
    (hasDerivAt_const (θ j) (0:ℂ)).congr_of_eventuallyEq hz
  exact hsum.unique hzero

/-- Intrinsic divergence in the first `n` angular coordinates is the ambient
divergence when the complete field is tangent. The eliminated coordinate
contributes exactly the minus derivative in the displayed formula. -/
theorem preferred_intrinsic_ambient_divergence {n : ℕ}
    (D : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (hcol : (∑ i, D i (Fin.last n)) = 0) :
    (∑ i : Fin n, (D i.castSucc i.castSucc-D i.castSucc (Fin.last n))) =
      ∑ i, D i i := by
  rw [Finset.sum_sub_distrib, Fin.sum_univ_castSucc]
  rw [Fin.sum_univ_castSucc] at hcol
  linear_combination -hcol

theorem preferred_actual_intrinsic_divergence {n : ℕ}
    (V : (Fin (n+1) → ℝ) → Fin (n+1) → ℂ) (θ : Fin (n+1) → ℝ)
    (D : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (htangent : ∀ᶠ x in 𝓝 θ, (∑ i, V x i) = 0)
    (hD : ∀ i j, HasDerivAt (fun u => V (Function.update θ j u) i) (D i j) (θ j)) :
    (∑ i : Fin n, (D i.castSucc i.castSucc-D i.castSucc (Fin.last n))) =
      ∑ i, D i i :=
  preferred_intrinsic_ambient_divergence D
    (preferred_tangent_derivative_sum V θ D htangent hD (Fin.last n))

end ConstrainedDivergence

/-! ## Concrete transported density and exact remaining global obligations -/
open scoped Topology

/-- The full occupancy Jacobian `I - i Dh`, using the actual real bump
first derivatives. No analytically continued cutoff occurs here. -/
def preferredContourMatrix {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (θ : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => (if i = j then 1 else 0) - Complex.I *
    (shiftJacobian τ (fun a => p (θ a)) (fun a => m (θ a))
      (fun a => deriv p (θ a)) (fun a => deriv m (θ a)) i j : ℝ)

theorem preferredContourMatrix_column_sum {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (θ : Fin N → ℝ) (j : Fin N) : (∑ i, preferredContourMatrix τ p m θ i j) = 1 := by
  simp only [preferredContourMatrix, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Complex.ofReal_sum,shiftJacobian_column_sum,Complex.ofReal_zero,mul_zero,sub_zero]
  simp

def preferredSourcePhase {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ) (s : ℂ)
    (θ : Fin N → ℝ) (i : Fin N) : ℂ :=
  preferredArccos (temperatureTrace s - Complex.cos (deformedAngles τ p m θ i))

def preferredSourceCoordinate {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ) (s : ℂ)
    (θ : Fin N → ℝ) (i : Fin N) : ℂ :=
  preferredSourcePhase τ p m s θ i + deformedAngles τ p m θ i - preferredMovingBranch s

def preferredSourceUDot (s q : ℂ) : ℂ := deriv (fun t => preferredMovingInverse t q) s

def preferredSourceUQ (s q : ℂ) : ℂ := deriv (preferredMovingInverse s) q

/-- The literal complete collective formula (7.12), evaluated in the actual
moving inverse. Its extension at the full-equality puncture is not assumed. -/
def preferredResidualCollective {N : ℕ} (s : ℂ) (q : Fin N → ℂ) : Fin N → ℂ :=
  collectiveField (fun i => preferredMovingInverse s (q i))
    (fun i => preferredSourceUDot s (q i)) (fun i => preferredSourceUQ s (q i))
    (-deriv preferredMovingBranch s)

def preferredResidualAnchor {N : ℕ} (s : ℂ) (q : Fin N → ℂ) (a : Fin N) : Fin N → ℂ :=
  anchorField (fun i => preferredSourceUDot s (q i))
    (fun i => preferredSourceUQ s (q i)) a

/-- Named cells are exactly the full right term or one fixed left anchor. -/
inductive PreferredTransportCell (N : ℕ) where
  | right
  | anchor (index : Fin N)

def preferredResidualField {N : ℕ} (cell : PreferredTransportCell N)
    (s : ℂ) (q : Fin N → ℂ) : Fin N → ℂ :=
  match cell with
  | .right => preferredResidualCollective s q
  | .anchor a => preferredResidualAnchor s q a

/-- The actual angular representative (7.6) on the coupled occupancy chart. -/
def preferredSourceAngularField {N : ℕ} (cell : PreferredTransportCell N)
    (τ : ℝ) (p m : ℝ → ℝ) (s : ℂ) (θ : Fin N → ℝ) : Fin N → ℂ :=
  let q := preferredSourceCoordinate τ p m s θ
  preferredAngularRepresentative (preferredContourMatrix τ p m θ)
    (fun i => preferredSourceUDot s (q i)) (fun i => preferredSourceUQ s (q i))
    (preferredResidualField cell s q)

/-- Literal lower one-sided weight after the complete deformation. -/
def preferredLowerWeight {N : ℕ} (η p m : ℝ → ℝ) (θ : Fin N → ℝ) : ℝ :=
  lowerWeight (η (occupancy p θ)) (η (occupancy m θ))

def preferredRightWeight {N : ℕ} (r : ℝ → ℝ) (θ : Fin N → ℝ) : ℝ :=
  ∏ i, r (θ i)

/-- The ordered telescope has exactly one fixed named left anchor. -/
def preferredAnchorWeight {N : ℕ} (r : ℝ → ℝ) (θ : Fin N → ℝ) (a : Fin N) : ℝ :=
  (1-r (θ a)) * ∏ j ∈ Finset.univ.filter (fun j : Fin N => j < a), r (θ j)

def preferredCellWeight {N : ℕ} (cell : PreferredTransportCell N)
    (η p m r : ℝ → ℝ) (θ : Fin N → ℝ) : ℝ :=
  preferredLowerWeight η p m θ * match cell with
    | .right => preferredRightWeight r θ
    | .anchor a => preferredAnchorWeight r θ a

theorem preferred_anchor_telescope {N : ℕ} (r : ℝ → ℝ) (θ : Fin N → ℝ) :
    preferredRightWeight r θ + (∑ a, preferredAnchorWeight r θ a) = 1 := by
  have h := Finset.prod_one_sub_ordered (Finset.univ : Finset (Fin N))
    (fun i => (1-r (θ i)))
  simp only [sub_sub_cancel] at h
  exact eq_sub_iff_add_eq.mp h

/-- Complete deformed physical scalar, with the physical root at every site
and all determinant factors. No tail envelope replaces this density. -/
def preferredDeformedPhysicalDensity {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (s : ℂ) (θ : Fin N → ℝ) : ℂ :=
  let w := deformedAngles τ p m θ
  let z := fun i => physicalRoot (temperatureTrace s-Complex.cos (w i))
  let Z := ∏ i, z i
  (1+Z)/(1-Z) * (gaugeKernel (fun i => Complex.exp (Complex.I*w i)) z).det *
    ∏ i, oneBody (z i)

/-- The source normalized scalar includes the exact constrained-Haar
normalization and the entire occupancy Jacobian. -/
def preferredPhysicalSeed {N : ℕ} (cell : PreferredTransportCell N) (τ : ℝ)
    (η p m r : ℝ → ℝ) (s : ℂ) (θ : Fin N → ℝ) : ℂ :=
  (preferredCellWeight cell η p m r θ : ℂ) * (preferredContourMatrix τ p m θ).det *
    preferredDeformedPhysicalDensity τ p m s θ /
    ((N.factorial : ℂ)*(2*Real.pi : ℂ)^(N-1))

/-- Ambient divergence uses real angular derivatives throughout. -/
def preferredAngularDivergence {N : ℕ} (F : (Fin N → ℝ) → Fin N → ℂ)
    (θ : Fin N → ℝ) : ℂ :=
  ∑ i, deriv (fun x : ℝ => F (Function.update θ i x) i) (θ i)

/-- Exact source sign: the angular field is subtracted. Equivalently this is
`∂s D + div((-V) D)`. Parameter derivatives are genuine complex derivatives. -/
def preferredTransportStep {N : ℕ}
    (V : ℂ → (Fin N → ℝ) → Fin N → ℂ)
    (D : ℂ → (Fin N → ℝ) → ℂ) (s : ℂ) (θ : Fin N → ℝ) : ℂ :=
  deriv (fun t : ℂ => D t θ) s -
    preferredAngularDivergence (fun x i => V s x i * D s x) θ

/-- The actual iterated density to be bounded in (7.20) and (8.10).
There is no norm bound or regularity premise in its definition. -/
def preferredTransportedDensity {N : ℕ} (cell : PreferredTransportCell N) (τ : ℝ)
    (η p m r : ℝ → ℝ) : ℕ → ℂ → (Fin N → ℝ) → ℂ
  | 0 => preferredPhysicalSeed cell τ η p m r
  | j+1 => preferredTransportStep (preferredSourceAngularField cell τ p m)
      (preferredTransportedDensity cell τ η p m r j)

theorem preferredTransportedDensity_zero {N : ℕ} (cell : PreferredTransportCell N)
    (τ : ℝ) (η p m r : ℝ → ℝ) :
    preferredTransportedDensity cell τ η p m r 0 = preferredPhysicalSeed cell τ η p m r := rfl

theorem preferredTransportedDensity_succ {N : ℕ} (cell : PreferredTransportCell N)
    (τ : ℝ) (η p m r : ℝ → ℝ) (j : ℕ) (s : ℂ) (θ : Fin N → ℝ) :
    preferredTransportedDensity cell τ η p m r (j+1) s θ =
      deriv (fun t : ℂ => preferredTransportedDensity cell τ η p m r j t θ) s -
      preferredAngularDivergence (fun x i => preferredSourceAngularField cell τ p m s x i *
        preferredTransportedDensity cell τ η p m r j s x) θ := rfl

/-- The actual first transport is derived by the complex parameter product
rule and the real angular product rule, retaining each real cutoff jet. -/
theorem preferredTransportStep_weighted {N : ℕ}
    (V : ℂ → (Fin N → ℝ) → Fin N → ℂ)
    (ω : (Fin N → ℝ) → ℝ) (G : ℂ → (Fin N → ℝ) → ℂ)
    (s : ℂ) (θ : Fin N → ℝ) (dω : Fin N → ℝ)
    (hG : DifferentiableAt ℂ (fun t => G t θ) s)
    (hω : ∀ i, HasDerivAt (fun u : ℝ => ω (Function.update θ i u)) (dω i) (θ i))
    (hflux : ∀ i, DifferentiableAt ℝ
      (fun u : ℝ => V s (Function.update θ i u) i * G s (Function.update θ i u)) (θ i)) :
    preferredTransportStep V (fun t x => (ω x : ℂ)*G t x) s θ =
      (ω θ : ℂ)*preferredTransportStep V G s θ -
        ∑ i, (dω i : ℂ)*V s θ i*G s θ := by
  have ht := (hG.hasDerivAt.const_mul (ω θ : ℂ)).deriv
  have hx (i : Fin N) := ((hω i).ofReal_comp.fun_mul (hflux i).hasDerivAt).deriv
  simp only [Function.update_eq_self] at hx
  have hfluxeq (i : Fin N) :
      (fun u : ℝ => V s (Function.update θ i u) i *
        ((ω (Function.update θ i u):ℂ)*G s (Function.update θ i u))) =
      (fun u : ℝ => (ω (Function.update θ i u):ℂ)*
        (V s (Function.update θ i u) i*G s (Function.update θ i u))) := by
    funext u
    ring
  unfold preferredTransportStep preferredAngularDivergence
  rw [ht]
  simp_rw [hfluxeq,hx]
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,mul_assoc]
  ring

/-- Both phase constraints for the literal source collective residual. -/
theorem preferredResidualCollective_constraints {N : ℕ} (s : ℂ) (q : Fin N → ℂ)
    (hc : ∀ i j, preferredSourceUQ s (q i)=preferredSourceUQ s (q j) →
      preferredMovingInverse s (q i)=preferredMovingInverse s (q j))
    (hR : collectiveDenominator (fun i => preferredMovingInverse s (q i)) ≠ 0) :
    (∑ i, preferredResidualCollective s q i) = -(N:ℂ)*deriv preferredMovingBranch s ∧
    (∑ i, preferredSourceUQ s (q i)*preferredResidualCollective s q i) =
      -(∑ i, preferredSourceUDot s (q i)) := by
  constructor
  · simp only [preferredResidualCollective,collectiveField_sum,Fintype.card_fin]
    ring
  · exact collectiveField_weighted_sum _ _ _ _ hc hR

theorem preferredResidualCollective_phase_freeze {N : ℕ} (s : ℂ) (q : Fin N → ℂ)
    (hc : ∀ i j, preferredSourceUQ s (q i)=preferredSourceUQ s (q j) →
      preferredMovingInverse s (q i)=preferredMovingInverse s (q j))
    (hR : collectiveDenominator (fun i => preferredMovingInverse s (q i)) ≠ 0) :
    (∑ i, ((1-preferredSourceUQ s (q i))*preferredResidualCollective s q i -
      preferredSourceUDot s (q i)+deriv preferredMovingBranch s)) = 0 := by
  obtain ⟨hphase,hangle⟩ := preferredResidualCollective_constraints s q hc hR
  exact movingPhase_transport_zero _ _ _ _ hangle (by simpa using hphase)

/-- A fixed regular-coordinate derivative on the original real angular
space. Smooth cutoffs are differentiated only by real angular derivatives. -/
def preferredCoordinateFrame {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ) (a : Fin N)
    (F : ℂ → (Fin N → ℝ) → ℂ) (s : ℂ) (θ : Fin N → ℝ) : ℂ :=
  ∑ i, (preferredContourMatrix τ p m θ)⁻¹ i a *
    preferredSourceUQ s (preferredSourceCoordinate τ p m s θ a) *
    deriv (fun x : ℝ => F s (Function.update θ i x)) (θ i)

/-- The exact fixed-q parameter frame; the plus sign is forced by
`∂s χ = - dot U / U_q`. -/
def preferredParameterFrame {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (F : ℂ → (Fin N → ℝ) → ℂ) (s : ℂ) (θ : Fin N → ℝ) : ℂ :=
  deriv (fun t : ℂ => F t θ) s +
    ∑ i, ((preferredContourMatrix τ p m θ)⁻¹.mulVec
      (fun a => preferredSourceUDot s (preferredSourceCoordinate τ p m s θ a))) i *
      deriv (fun x : ℝ => F s (Function.update θ i x)) (θ i)

/-- `none` means a fixed-q parameter derivative and `some a` means E_a. -/
def preferredFrameJet {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (F : ℂ → (Fin N → ℝ) → ℂ) : List (Option (Fin N)) → ℂ → (Fin N → ℝ) → ℂ
  | [] => F
  | none::xs => preferredParameterFrame τ p m (preferredFrameJet τ p m F xs)
  | some a::xs => preferredCoordinateFrame τ p m a (preferredFrameJet τ p m F xs)

def preferredCoordinateJetOrder {N : ℕ} (xs : List (Option (Fin N))) : ℕ :=
  xs.countP Option.isSome

def preferredRightAngularBox (d : PreferredBranchData) (δ δB : ℝ) (N : ℕ) :
    Set (Fin N → ℝ) := {θ | ∀ i, θ i ∈ Set.Icc (-d.b-δB) δ}

def preferredAngularDiameter {N : ℕ} (θ : Fin N → ℝ) : ℝ := Metric.diam (Set.range θ)

/-- Exact remaining P5/P6 global inverse obligation. This is a proposition,
not an axiom or a field assumed by a theorem. It quantifies one common compact
convex q-domain, its curvature margin, and the actual coupled contour images. -/
def PreferredGlobalRightInverse (d : PreferredBranchData) (τ : ℝ) (p m : ℝ → ℝ)
    (δ δB ε₀ : ℝ) : Prop :=
  ∃ D : Set ℂ, ∃ ρ c : ℝ, IsCompact D ∧ Convex ℝ D ∧ 0 ∈ interior D ∧
    0 < ρ ∧ 0 < c ∧
    (∀ s q, ‖s-preferredSelectedPoint d‖ < ρ → q ∈ D →
      AnalyticAt ℂ (fun x : ℂ × ℂ => preferredMovingInverse x.1 x.2) (s,q) ∧
      c ≤ (deriv (fun v => preferredSourceUQ s v) q).re) ∧
    (∀ (N : ℕ), 2 ≤ N → ∀ ε θ, 0 < ε → ε < ε₀ →
      θ ∈ preferredRightAngularBox d δ δB N → ∀ i,
      let s := IsingBulk.Branch.radialParameter d.alpha ε
      let q := preferredSourceCoordinate τ p m s θ i
      q ∈ interior D ∧ preferredMovingInverse s q = deformedAngles τ p m θ i ∧
      Complex.exp (-Complex.I*preferredSourcePhase τ p m s θ i) =
        physicalRoot (temperatureTrace s-Complex.cos (deformedAngles τ p m θ i)))

/-- Source-specific residual for (7.14). Every jet is the actual fixed-q
frame on the original real contour; the exponent counts only coordinate
jets, so no epsilon cost or parameter-derivative diameter cost is hidden. -/
def PreferredGlobalCollectiveJetBound (d : PreferredBranchData) (τ : ℝ)
    (p m : ℝ → ℝ) (δ δB ε₀ : ℝ) : Prop :=
  ∀ j : ℕ, ∃ C : ℝ, ∃ J : ℕ, 0 < C ∧
    ∀ (N : ℕ), 2 ≤ N → ∀ ε θ, 0 < ε → ε < ε₀ →
    θ ∈ preferredRightAngularBox d δ δB N → 0 < preferredAngularDiameter θ →
    ∀ xs : List (Option (Fin N)), xs.length ≤ j → ∀ i : Fin N,
    let s := IsingBulk.Branch.radialParameter d.alpha ε
    ‖preferredFrameJet τ p m
      (fun t x => preferredResidualCollective t (preferredSourceCoordinate τ p m t x) i)
      xs s θ‖ +
    ‖preferredFrameJet τ p m (fun t x => preferredSourceAngularField .right τ p m t x i)
      xs s θ‖ ≤ C*(N:ℝ)^J/(preferredAngularDiameter θ)^(1+preferredCoordinateJetOrder xs)

/-- The actual inverse-coordinate phase, one-body quotient, and complete
half-angle kernel. At singular artificial points the quotients are totalized;
regular extension there is a separate stated obligation. On the actual
positive-epsilon contour the denominators must be proved nonzero. -/
def preferredRegularPhase (s q : ℂ) : ℂ := q-preferredMovingInverse s q+preferredMovingBranch s

def preferredRegularOneBody (s q : ℂ) : ℂ :=
  preferredSourceUQ s q / Complex.sinh (Complex.I*preferredRegularPhase s q)

def preferredRegularKernel {N : ℕ} (s : ℂ) (q : Fin N → ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => Complex.sin ((preferredMovingInverse s (q i)-preferredMovingInverse s (q j))/2) /
    Complex.sinh (Complex.I*(preferredRegularPhase s (q i)+preferredRegularPhase s (q j))/2)

def preferredRegularProductPhase {N : ℕ} (s : ℂ) (q : Fin N → ℂ) : ℂ :=
  Complex.exp (-Complex.I*∑ i, preferredRegularPhase s (q i))

def preferredRegularAmplitude {N : ℕ} (s : ℂ) (q : Fin N → ℂ) : ℂ :=
  let Z := preferredRegularProductPhase s q
  (1+Z)/(1-Z) * (preferredRegularKernel s q).det *
    (∏ i, preferredRegularOneBody s (q i)) /
      ((N.factorial:ℂ)*(2*Real.pi:ℂ)^(N-1))

def preferredCoordinateJacobian {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (s : ℂ) (θ : Fin N → ℝ) : ℂ :=
  (preferredContourMatrix τ p m θ).det *
    ∏ i, (preferredSourceUQ s (preferredSourceCoordinate τ p m s θ i))⁻¹

open scoped Matrix.Norms.Elementwise in
/-- The determinant polynomial differentiated in the marked matrix entries.
For distinct rows and columns this is the signed complementary minor; repeated
marks causing coincident rows/columns give zero by the determinant algebra. -/
def preferredMarkedMinor {N : ℕ} (K : Matrix (Fin N) (Fin N) ℂ)
    (marks : List (Fin N × Fin N)) : ℂ :=
  iteratedFDeriv ℂ marks.length Matrix.det K (fun j =>
    Matrix.single (marks.get j).1 (marks.get j).2 (1:ℂ))

/-- Exact remaining marked-minor filtration for the actual iterated density.
A pointwise finite expansion, not an abstract tail envelope, carries both the
complementary minors and the required `h + ell ≤ 2*j` budget. -/
def PreferredMarkedMinorFiltration (d : PreferredBranchData) (τ : ℝ)
    (η p m r : ℝ → ℝ) (δ δB ε₀ : ℝ) : Prop :=
  ∀ j : ℕ, ∃ C : ℝ, ∃ J : ℕ, 0 < C ∧
    ∀ (N : ℕ), 2 ≤ N → ∀ ε θ, 0 < ε → ε < ε₀ →
    θ ∈ preferredRightAngularBox d δ δB N → 0 < preferredAngularDiameter θ →
    let s := IsingBulk.Branch.radialParameter d.alpha ε
    let q := preferredSourceCoordinate τ p m s θ
    ∃ T : Finset (ℕ × List (Fin N × Fin N)), ∃ a : (ℕ × List (Fin N × Fin N)) → ℂ,
      (T.card:ℝ) ≤ C*(N:ℝ)^J ∧
      (∀ z ∈ T, z.1+z.2.length ≤ 2*j ∧
        ‖a z‖ ≤ C^N*(N:ℝ)^J/(preferredAngularDiameter θ)^z.1) ∧
      preferredTransportedDensity .right τ η p m r j s θ =
        preferredCoordinateJacobian τ p m s θ /
          (((N.factorial:ℂ)*(2*Real.pi:ℂ)^(N-1))*(1-preferredRegularProductPhase s q)) *
          ∑ z ∈ T, a z*preferredMarkedMinor (preferredRegularKernel s q) z.2

/-- The manuscript’s actual one-sided angular lift. The omitted part of this
period interval is the upper plateau on which the lower weight vanishes. -/
def preferredLiftedAngles {N : ℕ} (δ : ℝ) (θ : Fin N → ℝ) : Fin N → ℝ :=
  fun i => toIocMod (by positivity : 0 < 2*Real.pi) (-Real.pi-δ) (θ i)

/-- Exact normalized integral of the j-times transported source density,
evaluated on the selected angular lift rather than a fictitious globally
periodic inverse coordinate. -/
def preferredTransportedIntegral {n : ℕ} (cell : PreferredTransportCell (n+1))
    (δ τ : ℝ) (η p m r : ℝ → ℝ) (j : ℕ) (s : ℂ) : ℂ :=
  ∫ θ in angularBox n,
    preferredTransportedDensity cell τ η p m r j s (preferredLiftedAngles δ (constrainedAngles θ))

/-- Remaining transport/integration obligation, including periodic boundary
cancellation and vanishing of the full-equality puncture flux. It concerns the
actual recurrence and the complete constrained integral. -/
def PreferredTransportIntegralIdentity (d : PreferredBranchData) (δ τ : ℝ)
    (η p m r : ℝ → ℝ) (Nstar k : ℕ) (ε₀ : ℝ) : Prop :=
  ∀ n : ℕ, Nstar+2 ≤ n+1 → Even (n+1) → ∀ j : ℕ, j ≤ k →
    ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ cell : PreferredTransportCell (n+1),
    iteratedDeriv j (preferredTransportedIntegral cell δ τ η p m r 0)
      (IsingBulk.Branch.radialParameter d.alpha ε) =
    preferredTransportedIntegral cell δ τ η p m r j (IsingBulk.Branch.radialParameter d.alpha ε)


/-- Exact finite right/left telescope of the complete one-sided weight. -/
theorem preferredCellWeight_sum {N : ℕ} (η p m r : ℝ → ℝ) (θ : Fin N → ℝ) :
    preferredCellWeight .right η p m r θ +
      (∑ a, preferredCellWeight (.anchor a) η p m r θ) = preferredLowerWeight η p m θ := by
  simp only [preferredCellWeight,← Finset.mul_sum,← mul_add,preferred_anchor_telescope,mul_one]

theorem preferredPhysicalSeed_sum {N : ℕ} (τ : ℝ) (η p m r : ℝ → ℝ)
    (s : ℂ) (θ : Fin N → ℝ) :
    preferredPhysicalSeed .right τ η p m r s θ +
      (∑ a, preferredPhysicalSeed (.anchor a) τ η p m r s θ) =
      (preferredLowerWeight η p m θ : ℂ)*(preferredContourMatrix τ p m θ).det *
        preferredDeformedPhysicalDensity τ p m s θ /
          ((N.factorial:ℂ)*(2*Real.pi:ℂ)^(N-1)) := by
  simp only [preferredPhysicalSeed,← Finset.sum_div,← Finset.sum_mul,← Complex.ofReal_sum,
    ← add_div,← add_mul,← Complex.ofReal_add,preferredCellWeight_sum]

/-- The literal deformed physical density returns to the actual original
angular density when the displacement is zero. -/
theorem preferredDeformedPhysicalDensity_zero {N : ℕ} (p m : ℝ → ℝ)
    (s : ℂ) (θ : Fin N → ℝ) :
    preferredDeformedPhysicalDensity 0 p m s θ = fullAngularDensity s θ := by
  simp only [preferredDeformedPhysicalDensity,deformedAngles,balancedShift,zero_div,zero_mul,
    Complex.ofReal_zero,mul_zero,sub_zero,← Complex.ofReal_cos,fullAngularDensity,
    angularRoots,angularW,angleRoot]
  rfl

/-- The matrix in the transported density is the actual differential of the
coupled occupancy deformation, including both global occupancy derivatives. -/
theorem preferred_deformedAngle_hasDerivAt {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (hp : Differentiable ℝ p) (hm : Differentiable ℝ m)
    (θ : Fin N → ℝ) (i j : Fin N) :
    HasDerivAt (fun x : ℝ => deformedAngles τ p m (Function.update θ j x) i)
      (preferredContourMatrix τ p m θ i j) (θ j) := by
  have hθ (a : Fin N) : HasDerivAt (fun x : ℝ => Function.update θ j x a)
      (if a=j then 1 else 0) (θ j) := by
    by_cases ha : a=j
    · subst a
      convert! hasDerivAt_id (θ j) using 1 <;> simp
      rfl
    · convert! hasDerivAt_const (θ j) (θ a) using 1 <;> simp [ha]
  have hp' (a : Fin N) : HasDerivAt (fun x : ℝ => p (Function.update θ j x a))
      (if a=j then deriv p (θ a) else 0) (θ j) := by
    convert! ((hp (θ a)).hasDerivAt.comp_of_eq (θ j) (hθ a)
      (by simp only [Function.update_eq_self])) using 1
    split_ifs <;> simp_all
  have hm' (a : Fin N) : HasDerivAt (fun x : ℝ => m (Function.update θ j x a))
      (if a=j then deriv m (θ a) else 0) (θ j) := by
    convert! ((hm (θ a)).hasDerivAt.comp_of_eq (θ j) (hθ a)
      (by simp only [Function.update_eq_self])) using 1
    split_ifs <;> simp_all
  have hP : HasDerivAt (fun x : ℝ => occupancy p (Function.update θ j x))
      (deriv p (θ j)) (θ j) := by
    simpa only [occupancy,Finset.sum_ite_eq',Finset.mem_univ,ite_true] using
      HasDerivAt.fun_sum (fun a (_ : a ∈ Finset.univ) => hp' a)
  have hQ : HasDerivAt (fun x : ℝ => occupancy m (Function.update θ j x))
      (deriv m (θ j)) (θ j) := by
    simpa only [occupancy,Finset.sum_ite_eq',Finset.mem_univ,ite_true] using
      HasDerivAt.fun_sum (fun a (_ : a ∈ Finset.univ) => hm' a)
  have hh := ((hP.mul (hm' i)).sub (hQ.mul (hp' i))).const_mul (τ/(N:ℝ))
  have hfull := (hθ i).ofReal_comp.sub (hh.ofReal_comp.const_mul Complex.I)
  simp only [Function.update_eq_self] at hfull
  convert! hfull using 1
  simp only [preferredContourMatrix,shiftJacobian,occupancy]
  split_ifs <;> push_cast <;> ring

/-- Tangency of every actual collective transported flux follows from the
source matrix columns and the two already-proved collective constraints. -/
theorem preferredSourceAngularField_right_tangent {N : ℕ}
    (τ : ℝ) (p m : ℝ → ℝ) (s : ℂ) (θ : Fin N → ℝ)
    (hM : (preferredContourMatrix τ p m θ).det ≠ 0)
    (hc : ∀ i j,
      preferredSourceUQ s (preferredSourceCoordinate τ p m s θ i)=
        preferredSourceUQ s (preferredSourceCoordinate τ p m s θ j) →
      preferredMovingInverse s (preferredSourceCoordinate τ p m s θ i)=
        preferredMovingInverse s (preferredSourceCoordinate τ p m s θ j))
    (hR : collectiveDenominator
      (fun i => preferredMovingInverse s (preferredSourceCoordinate τ p m s θ i)) ≠ 0) :
    (∑ i, preferredSourceAngularField .right τ p m s θ i)=0 := by
  exact preferredAngularRepresentative_tangent _ _ _ _
    (preferredContourMatrix_column_sum τ p m θ) hM
    (preferredResidualCollective_constraints s (preferredSourceCoordinate τ p m s θ) hc hR).2

theorem preferredSourceAngularField_anchor_tangent {N : ℕ}
    (τ : ℝ) (p m : ℝ → ℝ) (s : ℂ) (θ : Fin N → ℝ) (a : Fin N)
    (hM : (preferredContourMatrix τ p m θ).det ≠ 0)
    (ha : preferredSourceUQ s (preferredSourceCoordinate τ p m s θ a) ≠ 0) :
    (∑ i, preferredSourceAngularField (.anchor a) τ p m s θ i)=0 := by
  exact preferredAngularRepresentative_tangent _ _ _ _
    (preferredContourMatrix_column_sum τ p m θ) hM (anchorField_weighted_sum _ _ _ ha)



end
end IsingBulk.Preferred22
