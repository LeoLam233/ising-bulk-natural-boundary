import IsingBulk.Preferred22.PfaffianFoundation.Congruence
import Mathlib.Tactic
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# LT22 Preferred: the four-point dispersion identity

This file implements the algebra in Lemma 4.1 of the frozen 22-page
manuscript.  The cleared identity is valid even when a pair denominator
vanishes.  The rational identity explicitly requires the six denominators
to be nonzero.  No Pfaffian identity or complete-series conclusion is an
assumption of these declarations.
-/

namespace IsingBulk.Preferred22

section FourPoint

variable {𝕜 : Type*} [Field 𝕜]

/-- The six-factor Vandermonde in the manuscript's sign convention. -/
def vandermonde4 (a b c d : 𝕜) : 𝕜 :=
  (a - b) * (a - c) * (a - d) * (b - c) * (b - d) * (c - d)

/-- The common symmetric remainder in the proof of Lemma 4.1. -/
def dispersionR4 (a b c d : 𝕜) : 𝕜 :=
  a * b * c * d + (a * b * c * d)⁻¹ + 2 -
    ((a * b + (a * b)⁻¹) + (a * c + (a * c)⁻¹) +
     (a * d + (a * d)⁻¹) + (b * c + (b * c)⁻¹) +
     (b * d + (b * d)⁻¹) + (c * d + (c * d)⁻¹))

/-- The cancellation of the common symmetric term is an exact polynomial identity. -/
theorem plucker_difference4 (a b c d : 𝕜) :
    (a - b) * (c - d) - (a - c) * (b - d) + (a - d) * (b - c) = 0 := by
  ring

/-- The cross-factor decomposition used before the Vandermonde reduction. -/
theorem dispersion_cross4 (a b c d : 𝕜)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) :
    (1 - a * c) * (1 - a * d) * (1 - b * c) * (1 - b * d) =
    (a * b * c * d) *
      (dispersionR4 a b c d + (a + a⁻¹) * (b + b⁻¹) +
        (c + c⁻¹) * (d + d⁻¹)) := by
  unfold dispersionR4
  field_simp
  ring

/-- Changing the two middle arguments leaves the common remainder unchanged. -/
theorem dispersionR4_swap_middle (a b c d : 𝕜) :
    dispersionR4 a c b d = dispersionR4 a b c d := by
  unfold dispersionR4
  simp only [mul_inv_rev]
  ring

/-- The other partition of four labels has the same common remainder. -/
theorem dispersionR4_rotate_last (a b c d : 𝕜) :
    dispersionR4 a d b c = dispersionR4 a b c d := by
  unfold dispersionR4
  simp only [mul_inv_rev]
  ring

/-- The determinant reduction in Lemma 4.1, expressed without determinant notation. -/
theorem dispersion_vandermonde4 (S a b c d : 𝕜)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) :
    (a - b) * (c - d) *
        ((2*S - a - a⁻¹) * (2*S - b - b⁻¹) +
         (2*S - c - c⁻¹) * (2*S - d - d⁻¹)) -
    (a - c) * (b - d) *
        ((2*S - a - a⁻¹) * (2*S - c - c⁻¹) +
         (2*S - b - b⁻¹) * (2*S - d - d⁻¹)) +
    (a - d) * (b - c) *
        ((2*S - a - a⁻¹) * (2*S - d - d⁻¹) +
         (2*S - b - b⁻¹) * (2*S - c - c⁻¹)) =
      vandermonde4 a b c d / (a*b*c*d) := by
  unfold vandermonde4
  field_simp
  ring

/-- Lemma 4.1 after clearing the six pair denominators.
No assumption says that these pair denominators are nonzero. -/
theorem four_point_dispersion_cleared
    (S y1 y2 y3 y4 z1 z2 z3 z4 : 𝕜)
    (hy1 : y1 ≠ 0) (hy2 : y2 ≠ 0) (hy3 : y3 ≠ 0) (hy4 : y4 ≠ 0)
    (hz1 : z1 ≠ 0) (hz2 : z2 ≠ 0) (hz3 : z3 ≠ 0) (hz4 : z4 ≠ 0)
    (h1 : y1 + y1⁻¹ + z1 + z1⁻¹ = 2*S)
    (h2 : y2 + y2⁻¹ + z2 + z2⁻¹ = 2*S)
    (h3 : y3 + y3⁻¹ + z3 + z3⁻¹ = 2*S)
    (h4 : y4 + y4⁻¹ + z4 + z4⁻¹ = 2*S) :
    (y1-y2)*(y3-y4)*((1-z1*z3)*(1-z1*z4)*(1-z2*z3)*(1-z2*z4)) -
    (y1-y3)*(y2-y4)*((1-z1*z2)*(1-z1*z4)*(1-z2*z3)*(1-z3*z4)) +
    (y1-y4)*(y2-y3)*((1-z1*z2)*(1-z1*z3)*(1-z2*z4)*(1-z3*z4)) =
    (z1*z2*z3*z4) * vandermonde4 y1 y2 y3 y4 / (y1*y2*y3*y4) := by
  have ht1 : z1 + z1⁻¹ = 2*S-y1-y1⁻¹ := by linear_combination h1
  have ht2 : z2 + z2⁻¹ = 2*S-y2-y2⁻¹ := by linear_combination h2
  have ht3 : z3 + z3⁻¹ = 2*S-y3-y3⁻¹ := by linear_combination h3
  have ht4 : z4 + z4⁻¹ = 2*S-y4-y4⁻¹ := by linear_combination h4
  have h12 := dispersion_cross4 z1 z2 z3 z4 hz1 hz2 hz3 hz4
  have h13 := dispersion_cross4 z1 z3 z2 z4 hz1 hz3 hz2 hz4
  have h14 := dispersion_cross4 z1 z4 z2 z3 hz1 hz4 hz2 hz3
  rw [dispersionR4_swap_middle] at h13
  rw [dispersionR4_rotate_last] at h14
  have hp := plucker_difference4 y1 y2 y3 y4
  have hv := dispersion_vandermonde4 S y1 y2 y3 y4 hy1 hy2 hy3 hy4
  rw [ht1, ht2, ht3, ht4] at h12 h13 h14
  linear_combination
    (y1-y2)*(y3-y4)*h12 -
    (y1-y3)*(y2-y4)*h13 +
    (y1-y4)*(y2-y3)*h14 +
    (z1*z2*z3*z4)*dispersionR4 z1 z2 z3 z4*hp +
    (z1*z2*z3*z4)*hv

/-- The rational entry used in Lemma 4.1. -/
def dispersionB (yi yj zi zj : 𝕜) : 𝕜 := (yi-yj)/(1-zi*zj)

/-- Clearing six independent pair denominators, kept abstract to avoid expanding
large rational dispersion polynomials during simplification. -/
theorem four_fraction_of_cleared
    (a b c d e f A B C D E F w : 𝕜)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hD : D ≠ 0) (hE : E ≠ 0) (hF : F ≠ 0)
    (h : a*f*(B*C*D*E)-b*e*(A*C*D*F)+c*d*(A*B*E*F) =
      w*(a*b*c*d*e*f)) :
    (a/A)*(f/F)-(b/B)*(e/E)+(c/C)*(d/D) =
      w*((a/A)*(b/B)*(c/C)*(d/D)*(e/E)*(f/F)) := by
  field_simp
  linear_combination h

/-- Lemma 4.1 as stated, on the locus where its rational expressions are defined. -/
theorem four_point_dispersion
    (S y1 y2 y3 y4 z1 z2 z3 z4 : 𝕜)
    (hy1 : y1 ≠ 0) (hy2 : y2 ≠ 0) (hy3 : y3 ≠ 0) (hy4 : y4 ≠ 0)
    (hz1 : z1 ≠ 0) (hz2 : z2 ≠ 0) (hz3 : z3 ≠ 0) (hz4 : z4 ≠ 0)
    (h1 : y1 + y1⁻¹ + z1 + z1⁻¹ = 2*S)
    (h2 : y2 + y2⁻¹ + z2 + z2⁻¹ = 2*S)
    (h3 : y3 + y3⁻¹ + z3 + z3⁻¹ = 2*S)
    (h4 : y4 + y4⁻¹ + z4 + z4⁻¹ = 2*S)
    (h12 : 1-z1*z2 ≠ 0) (h13 : 1-z1*z3 ≠ 0) (h14 : 1-z1*z4 ≠ 0)
    (h23 : 1-z2*z3 ≠ 0) (h24 : 1-z2*z4 ≠ 0) (h34 : 1-z3*z4 ≠ 0) :
    dispersionB y1 y2 z1 z2 * dispersionB y3 y4 z3 z4 -
    dispersionB y1 y3 z1 z3 * dispersionB y2 y4 z2 z4 +
    dispersionB y1 y4 z1 z4 * dispersionB y2 y3 z2 z3 =
      ((z1/y1)*(z2/y2)*(z3/y3)*(z4/y4)) *
      (dispersionB y1 y2 z1 z2 * dispersionB y1 y3 z1 z3 *
       dispersionB y1 y4 z1 z4 * dispersionB y2 y3 z2 z3 *
       dispersionB y2 y4 z2 z4 * dispersionB y3 y4 z3 z4) := by
  have h := four_point_dispersion_cleared S y1 y2 y3 y4 z1 z2 z3 z4
    hy1 hy2 hy3 hy4 hz1 hz2 hz3 hz4 h1 h2 h3 h4
  unfold dispersionB
  apply four_fraction_of_cleared _ _ _ _ _ _ _ _ _ _ _ _ _
    h12 h13 h14 h23 h24 h34
  rw [h]
  unfold vandermonde4
  simp only [div_mul_div_comm]
  ring

/-- The scalar factorization/cancellation step in the Pfaffian induction.
The Pfaffian condensation identity itself is a separate obligation. -/
theorem condensation_product_cancellation
    (P F Q T a b c d e f : 𝕜) (hP : P ≠ 0)
    (hcond : F*P = P^2*Q*(a*f-b*e+c*d))
    (hfour : a*f-b*e+c*d = a*b*c*d*e*f)
    (hprod : T = P*Q*(a*b*c*d*e*f)) : F = T := by
  apply mul_right_cancel₀ hP
  rw [hcond, hfour, hprod]
  ring

end FourPoint

section PairElimination

open Matrix
open scoped Matrix

variable {𝕜 : Type*} [Field 𝕜]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The exact two-anchor Schur-complement reduction supplied by the four-point
identity.  This is an arbitrary-size determinant reduction, not an assumed
Pfaffian condensation theorem. -/
theorem determinant_pair_elimination
    (a : 𝕜) (ha : a ≠ 0) (u v : ι → 𝕜) (D : Matrix ι ι 𝕜)
    (hfour : ∀ i j, a * D i j - u i * v j + u j * v i =
      a * u i * u j * v i * v j * D i j) :
    (Matrix.fromBlocks (!![0,a; -a,0])
      (fun i j => if i = (0 : Fin 2) then u j else v j)
      (fun i j => if j = (0 : Fin 2) then -u i else -v i) D).det =
      a^2 * (∏ i, u i * v i)^2 * D.det := by
  let A : Matrix (Fin 2) (Fin 2) 𝕜 := !![0,a; -a,0]
  let AI : Matrix (Fin 2) (Fin 2) 𝕜 := !![0,-a⁻¹; a⁻¹,0]
  let B : Matrix (Fin 2) ι 𝕜 := fun i j => if i = 0 then u j else v j
  let C : Matrix ι (Fin 2) 𝕜 := fun i j => if j = 0 then -u i else -v i
  let d : ι → 𝕜 := fun i => u i * v i
  let : Invertible A :=
    { invOf := AI
      invOf_mul_self := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [A, AI, Matrix.mul_apply, Fin.sum_univ_two, ha]
      mul_invOf_self := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [A, AI, Matrix.mul_apply, Fin.sum_univ_two, ha] }
  have hschur : D - C * ⅟A * B = Matrix.diagonal d * D * Matrix.diagonal d := by
    change D - C * AI * B = _
    ext i j
    simp only [Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
    change D i j - (∑ k : Fin 2, (∑ l : Fin 2, C i l * AI l k) * B k j) =
      d i * D i j * d j
    simp [Fin.sum_univ_two, C, AI, B, d]
    field_simp
    linear_combination hfour i j
  change (Matrix.fromBlocks A B C D).det = _
  rw [Matrix.det_fromBlocks₁₁, hschur, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_diagonal]
  have hdetA : A.det = a^2 := by
    simp [A, Matrix.det_fin_two]
    ring
  rw [hdetA]
  dsimp [d]
  ring

end PairElimination

section PhysicalScaling

/-- The local square-root representation of the physical angular kernel. -/
def scaledPair (ri rj Bij : ℂ) : ℂ := -Complex.I * ri * rj * Bij

/-- Four-point propagation hypothesis for the actual complex kernel.
The scalar B identity is converted with exactly the four local square roots. -/
theorem scaled_four_point
    (r1 r2 r3 r4 b12 b13 b14 b23 b24 b34 : ℂ)
    (hB : b12*b34-b13*b24+b14*b23 =
      (r1^2*r2^2*r3^2*r4^2)*(b12*b13*b14*b23*b24*b34)) :
    scaledPair r1 r2 b12 * scaledPair r3 r4 b34 -
      scaledPair r1 r3 b13 * scaledPair r2 r4 b24 +
      scaledPair r1 r4 b14 * scaledPair r2 r3 b23 =
    scaledPair r1 r2 b12 * scaledPair r1 r3 b13 *
      scaledPair r1 r4 b14 * scaledPair r2 r3 b23 *
      scaledPair r2 r4 b24 * scaledPair r3 r4 b34 := by
  unfold scaledPair
  linear_combination
    (Complex.I^2*r1*r2*r3*r4)*hB +
    (Complex.I^2*(1-Complex.I^2)*(r1*r2*r3*r4)^3*
      (b12*b13*b14*b23*b24*b34))*Complex.I_sq

/-- Proposition 4.3's four-point physical-kernel identity, with all domain hypotheses. -/
theorem four_point_physical
    (S y1 y2 y3 y4 z1 z2 z3 z4 r1 r2 r3 r4 : ℂ)
    (hy1 : y1 ≠ 0) (hy2 : y2 ≠ 0) (hy3 : y3 ≠ 0) (hy4 : y4 ≠ 0)
    (hz1 : z1 ≠ 0) (hz2 : z2 ≠ 0) (hz3 : z3 ≠ 0) (hz4 : z4 ≠ 0)
    (h1 : y1+y1⁻¹+z1+z1⁻¹ = 2*S) (h2 : y2+y2⁻¹+z2+z2⁻¹ = 2*S)
    (h3 : y3+y3⁻¹+z3+z3⁻¹ = 2*S) (h4 : y4+y4⁻¹+z4+z4⁻¹ = 2*S)
    (h12 : 1-z1*z2 ≠ 0) (h13 : 1-z1*z3 ≠ 0) (h14 : 1-z1*z4 ≠ 0)
    (h23 : 1-z2*z3 ≠ 0) (h24 : 1-z2*z4 ≠ 0) (h34 : 1-z3*z4 ≠ 0)
    (hr1 : r1^2 = z1/y1) (hr2 : r2^2 = z2/y2)
    (hr3 : r3^2 = z3/y3) (hr4 : r4^2 = z4/y4) :
    scaledPair r1 r2 (dispersionB y1 y2 z1 z2) *
      scaledPair r3 r4 (dispersionB y3 y4 z3 z4) -
    scaledPair r1 r3 (dispersionB y1 y3 z1 z3) *
      scaledPair r2 r4 (dispersionB y2 y4 z2 z4) +
    scaledPair r1 r4 (dispersionB y1 y4 z1 z4) *
      scaledPair r2 r3 (dispersionB y2 y3 z2 z3) =
    scaledPair r1 r2 (dispersionB y1 y2 z1 z2) *
      scaledPair r1 r3 (dispersionB y1 y3 z1 z3) *
      scaledPair r1 r4 (dispersionB y1 y4 z1 z4) *
      scaledPair r2 r3 (dispersionB y2 y3 z2 z3) *
      scaledPair r2 r4 (dispersionB y2 y4 z2 z4) *
      scaledPair r3 r4 (dispersionB y3 y4 z3 z4) := by
  apply scaled_four_point
  rw [hr1, hr2, hr3, hr4]
  exact four_point_dispersion S y1 y2 y3 y4 z1 z2 z3 z4
    hy1 hy2 hy3 hy4 hz1 hz2 hz3 hz4 h1 h2 h3 h4 h12 h13 h14 h23 h24 h34

/-- The positive real amplitude displayed at the end of Section 4. -/
noncomputable def localAmplitude (N : ℕ) (α : ℝ) : ℝ :=
  (2 / ((Nat.factorial N : ℝ) * (2*Real.pi)^(N-1))) *
    (2 : ℝ)^(-((N*(N-1) : ℕ) : ℤ)) * (Real.sin α)^(-((N^2 : ℕ) : ℤ))

theorem localAmplitude_pos (N : ℕ) {α : ℝ}
    (hα0 : 0 < α) (hαπ : α < Real.pi) : 0 < localAmplitude N α := by
  have hs : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hα0 hαπ
  unfold localAmplitude
  positivity

end PhysicalScaling

open Matrix
open scoped Matrix

variable {𝕜 : Type*} [Field 𝕜]

/-- The ordered off-diagonal product, convenient for permutation-free induction. -/
def offDiagProduct {ι : Type*} [Fintype ι] [DecidableEq ι] (K : Matrix ι ι 𝕜) : 𝕜 :=
  ∏ i, ∏ j, if i = j then 1 else K i j

theorem offDiagProduct_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ) (K : Matrix κ κ 𝕜) :
    offDiagProduct (K.submatrix e e) = offDiagProduct K := by
  unfold offDiagProduct
  apply Fintype.prod_equiv e
  intro i
  apply Fintype.prod_equiv e
  intro j
  simp [Matrix.submatrix_apply, e.injective.eq_iff]

theorem offDiagProduct_two_block {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : 𝕜) (u v : ι → 𝕜) (D : Matrix ι ι 𝕜) :
    offDiagProduct (Matrix.fromBlocks (!![0,a; -a,0])
      (fun i j => if i = (0 : Fin 2) then u j else v j)
      (fun i j => if j = (0 : Fin 2) then -u i else -v i) D) =
      -(a^2 * (∏ i, u i * v i)^2 * offDiagProduct D) := by
  simp only [offDiagProduct, Fintype.prod_sum_type, Fin.prod_univ_two]
  simp [Matrix.fromBlocks]
  simp only [Finset.prod_mul_distrib]
  ring

/-- Generic all-even-size determinant product implied by the four-point relation,
prior to continuation across a zero pair entry. -/
theorem determinant_product_generic (n : ℕ) (K : Matrix (Fin (2*n)) (Fin (2*n)) 𝕜)
    (hdiag : ∀ i, K i i = 0)
    (hskew : ∀ i j, K i j = -K j i)
    (hnz : ∀ i j, i ≠ j → K i j ≠ 0)
    (hfour : ∀ a b i j,
      K a b * K i j - K a i * K b j + K a j * K b i =
      K a b * K a i * K a j * K b i * K b j * K i j) :
    K.det = (-1)^n * offDiagProduct K := by
  induction n with
  | zero => simp [offDiagProduct]
  | succ n ih =>
    let e : (Fin 2 ⊕ Fin (2*n)) ≃ Fin (2*(n+1)) :=
      finSumFinEquiv.trans (finCongr (by omega))
    let a := K (e (.inl 0)) (e (.inl 1))
    let u : Fin (2*n) → 𝕜 := fun i => K (e (.inl 0)) (e (.inr i))
    let v : Fin (2*n) → 𝕜 := fun i => K (e (.inl 1)) (e (.inr i))
    let D : Matrix (Fin (2*n)) (Fin (2*n)) 𝕜 :=
      fun i j => K (e (.inr i)) (e (.inr j))
    have ha : a ≠ 0 := by
      apply hnz
      intro he
      have hh := e.injective he
      norm_num at hh
    have hDdiag : ∀ i, D i i = 0 := fun i => hdiag _
    have hDskew : ∀ i j, D i j = -D j i := fun i j => hskew _ _
    have hDnz : ∀ i j, i ≠ j → D i j ≠ 0 := by
      intro i j hij
      apply hnz
      intro he
      exact hij (Sum.inr.inj (e.injective he))
    have hDfour : ∀ a b i j,
        D a b * D i j - D a i * D b j + D a j * D b i =
        D a b * D a i * D a j * D b i * D b j * D i j := by
      intro a b i j
      exact hfour _ _ _ _
    have h10 : K (e (.inl 1)) (e (.inl 0)) = -a := hskew _ _
    have hC0 (i) : K (e (.inr i)) (e (.inl 0)) = -u i := hskew _ _
    have hC1 (i) : K (e (.inr i)) (e (.inl 1)) = -v i := hskew _ _
    have hblock : K.submatrix e e = Matrix.fromBlocks (!![0,a; -a,0])
        (fun i j => if i = (0 : Fin 2) then u j else v j)
        (fun i j => if j = (0 : Fin 2) then -u i else -v i) D := by
      ext i j
      rcases i with i | i <;> rcases j with j | j
      · fin_cases i <;> fin_cases j <;>
          simp [Matrix.fromBlocks, Matrix.submatrix_apply, a, hdiag, h10]
      · fin_cases i <;> simp [Matrix.fromBlocks, Matrix.submatrix_apply, u, v]
      · fin_cases j <;> simp [Matrix.fromBlocks, Matrix.submatrix_apply, hC0, hC1]
      · rfl
    have helim := determinant_pair_elimination a ha u v D
      (fun i j => hfour (e (.inl 0)) (e (.inl 1)) (e (.inr i)) (e (.inr j)))
    have hD := ih D hDdiag hDskew hDnz hDfour
    calc
      K.det = (K.submatrix e e).det := (Matrix.det_submatrix_equiv_self e K).symm
      _ = a^2 * (∏ i, u i * v i)^2 * D.det := by rw [hblock]; exact helim
      _ = (-1)^(n+1) * offDiagProduct (K.submatrix e e) := by
        rw [hblock, offDiagProduct_two_block, hD, pow_succ]
        ring
      _ = (-1)^(n+1) * offDiagProduct K := by rw [offDiagProduct_reindex]

/-- If a pair entry vanishes, the four-point equations force proportional rows. -/
theorem determinant_zero_of_four_point_collision {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι 𝕜) {a b : ι} (hab : a ≠ b) (hz : K a b = 0)
    (hfour : ∀ i j,
      K a b * K i j - K a i * K b j + K a j * K b i =
      K a b * K a i * K a j * K b i * K b j * K i j) : K.det = 0 := by
  by_cases hrow0 : ∀ i, K a i = 0
  · exact Matrix.det_eq_zero_of_row_eq_zero a hrow0
  · push Not at hrow0
    obtain ⟨c, hc⟩ := hrow0
    let t := K b c / K a c
    have hrow : K b = t • K a := by
      ext j
      change K b j = (K b c / K a c) * K a j
      have h := hfour c j
      rw [hz] at h
      field_simp
      linear_combination -h
    have hself : K.updateRow b (t • K a) = K := by
      rw [← hrow]
      exact Matrix.updateRow_eq_self K b
    calc
      K.det = (K.updateRow b (t • K a)).det := congrArg Matrix.det hself.symm
      _ = t * (K.updateRow b (K a)).det := Matrix.det_updateRow_smul K b t (K a)
      _ = 0 := by rw [Matrix.det_updateRow_eq_zero hab, mul_zero]

theorem offDiagProduct_zero_of_pair {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι 𝕜) {a b : ι} (hab : a ≠ b) (hz : K a b = 0) :
    offDiagProduct K = 0 := by
  unfold offDiagProduct
  apply Finset.prod_eq_zero (Finset.mem_univ a)
  apply Finset.prod_eq_zero (Finset.mem_univ b)
  simp [hab, hz]

/-- The exact all-even-size determinant product, including every zero pair locus.
Unlike a generic-only argument, the degenerate case is closed algebraically. -/
theorem determinant_product (n : ℕ) (K : Matrix (Fin (2*n)) (Fin (2*n)) 𝕜)
    (hdiag : ∀ i, K i i = 0)
    (hskew : ∀ i j, K i j = -K j i)
    (hfour : ∀ a b i j,
      K a b * K i j - K a i * K b j + K a j * K b i =
      K a b * K a i * K a j * K b i * K b j * K i j) :
    K.det = (-1)^n * offDiagProduct K := by
  by_cases hnz : ∀ i j, i ≠ j → K i j ≠ 0
  · exact determinant_product_generic n K hdiag hskew hnz hfour
  · push Not at hnz
    obtain ⟨a, b, hab, hz⟩ := hnz
    rw [determinant_zero_of_four_point_collision K hab hz (hfour a b),
      offDiagProduct_zero_of_pair K hab hz, mul_zero]

/-- The product over i < j, using the natural linear order on Fin N. -/
def upperPairProduct {N : ℕ} (K : Matrix (Fin N) (Fin N) 𝕜) : 𝕜 :=
  ∏ i, ∏ j ∈ Finset.Ioi i, K i j

theorem upperPairProduct_succ {N : ℕ} (K : Matrix (Fin (N+1)) (Fin (N+1)) 𝕜) :
    upperPairProduct K = (∏ j : Fin N, K 0 j.succ) *
      upperPairProduct (K.submatrix Fin.succ Fin.succ) := by
  unfold upperPairProduct
  rw [Fin.prod_univ_succ, Fin.prod_Ioi_zero]
  simp only [Fin.prod_Ioi_succ, Matrix.submatrix_apply]

theorem offDiagProduct_succ {N : ℕ} (K : Matrix (Fin (N+1)) (Fin (N+1)) 𝕜)
    (hskew : ∀ i j, K i j = -K j i) :
    offDiagProduct K = (-1)^N * (∏ j : Fin N, K 0 j.succ)^2 *
      offDiagProduct (K.submatrix Fin.succ Fin.succ) := by
  unfold offDiagProduct
  simp only [Fin.prod_univ_succ]
  have hz (i : Fin N) : (0 : Fin (N+1)) ≠ i.succ := (Fin.succ_ne_zero i).symm
  simp [hz]
  have hrows : (∏ i : Fin N, K i.succ 0) = (-1)^N * ∏ i : Fin N, K 0 i.succ := by
    calc
      _ = ∏ i : Fin N, (-1) * K 0 i.succ := by
        apply Finset.prod_congr rfl
        intro i hi
        rw [hskew i.succ 0]
        ring
      _ = _ := by rw [Finset.prod_mul_distrib]; simp
  simp only [Finset.prod_mul_distrib]
  rw [hrows]
  ring

theorem offDiagProduct_eq_upper {N : ℕ} (K : Matrix (Fin N) (Fin N) 𝕜)
    (hskew : ∀ i j, K i j = -K j i) :
    offDiagProduct K = (-1)^(N.choose 2) * (upperPairProduct K)^2 := by
  induction N with
  | zero => simp [offDiagProduct, upperPairProduct]
  | succ N ih =>
    rw [offDiagProduct_succ K hskew, upperPairProduct_succ,
      ih (K.submatrix Fin.succ Fin.succ) (fun i j => hskew _ _),
      Nat.choose_succ_succ, Nat.choose_one_right, pow_add]
    ring

theorem choose_two_even_sign (n : ℕ) :
    (-1 : 𝕜)^((2*n).choose 2) = (-1 : 𝕜)^n := by
  have hchoose : (2*n).choose 2 = n*(2*n-1) := by
    rw [Nat.choose_two_right,
      show (2*n)*(2*n-1) = (n*(2*n-1))*2 by ring]
    omega
  rw [hchoose]
  by_cases hn : n = 0
  · simp [hn]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have ho : Odd (2*n-1) := ⟨n-1, by omega⟩
    rw [Nat.mul_comm n, pow_mul, ho.neg_one_pow]

/-- The determinant formula in Proposition 4.3, at every even size and at collisions. -/
theorem determinant_squared_pair_product (n : ℕ)
    (K : Matrix (Fin (2*n)) (Fin (2*n)) 𝕜)
    (hdiag : ∀ i, K i i = 0)
    (hskew : ∀ i j, K i j = -K j i)
    (hfour : ∀ a b i j,
      K a b * K i j - K a i * K b j + K a j * K b i =
      K a b * K a i * K a j * K b i * K b j * K i j) :
    K.det = ∏ i, ∏ j ∈ Finset.Ioi i, K i j ^ 2 := by
  rw [determinant_product n K hdiag hskew hfour,
    offDiagProduct_eq_upper K hskew, choose_two_even_sign]
  have hs : (-1 : 𝕜)^n * (-1)^n = 1 := by
    rw [← mul_pow]
    simp
  calc
    _ = ((-1 : 𝕜)^n * (-1)^n) * (upperPairProduct K)^2 := by ring
    _ = (upperPairProduct K)^2 := by rw [hs, one_mul]
    _ = _ := by simp [upperPairProduct, Finset.prod_pow]

/-- The locally normalized kernel on the common dispersion curve. -/
noncomputable def dispersionMatrix {N : ℕ} (y z r : Fin N → ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => scaledPair (r i) (r j) (dispersionB (y i) (y j) (z i) (z j))

theorem dispersionMatrix_diagonal {N : ℕ} (y z r : Fin N → ℂ) (i : Fin N) :
    dispersionMatrix y z r i i = 0 := by
  simp [dispersionMatrix, scaledPair, dispersionB]

theorem dispersionMatrix_skew {N : ℕ} (y z r : Fin N → ℂ) (i j : Fin N) :
    dispersionMatrix y z r i j = -dispersionMatrix y z r j i := by
  unfold dispersionMatrix scaledPair dispersionB
  rw [mul_comm (z j) (z i)]
  ring

/-- Repeated indices make the four-point equation automatic for an alternating kernel. -/
theorem four_point_of_index_collision {ι : Type*} (K : ι → ι → 𝕜)
    (hdiag : ∀ i, K i i = 0) (hskew : ∀ i j, K i j = -K j i)
    (a b i j : ι)
    (hc : a=b ∨ a=i ∨ a=j ∨ b=i ∨ b=j ∨ i=j) :
    K a b * K i j - K a i * K b j + K a j * K b i =
      K a b * K a i * K a j * K b i * K b j * K i j := by
  rcases hc with h | h | h | h | h | h
  · subst b
    simp [hdiag]
    ring
  · subst i
    rw [hdiag, hskew b a]
    ring
  · subst j
    rw [hdiag, hskew i a, hskew b a]
    ring
  · subst i
    simp [hdiag]
  · subst j
    rw [hdiag, hskew i b]
    ring
  · subst j
    simp [hdiag]

/-- The physical dispersion determinant has the full squared pair product at
all even orders, including coincident points, without importing the old LT chain. -/
theorem dispersion_determinant_product (n : ℕ) (S : ℂ)
    (y z r : Fin (2*n) → ℂ)
    (hy : ∀ i, y i ≠ 0) (hz : ∀ i, z i ≠ 0)
    (hcurve : ∀ i, y i + (y i)⁻¹ + z i + (z i)⁻¹ = 2*S)
    (hden : ∀ i j, i ≠ j → 1-z i*z j ≠ 0)
    (hroot : ∀ i, r i^2 = z i / y i) :
    (dispersionMatrix y z r).det =
      ∏ i, ∏ j ∈ Finset.Ioi i, (dispersionMatrix y z r i j)^2 := by
  apply determinant_squared_pair_product n (dispersionMatrix y z r)
    (dispersionMatrix_diagonal y z r) (dispersionMatrix_skew y z r)
  intro a b i j
  by_cases hab : a=b
  · exact four_point_of_index_collision _ (dispersionMatrix_diagonal y z r)
      (dispersionMatrix_skew y z r) a b i j (Or.inl hab)
  by_cases hai : a=i
  · exact four_point_of_index_collision _ (dispersionMatrix_diagonal y z r)
      (dispersionMatrix_skew y z r) a b i j (Or.inr (Or.inl hai))
  by_cases haj : a=j
  · exact four_point_of_index_collision _ (dispersionMatrix_diagonal y z r)
      (dispersionMatrix_skew y z r) a b i j (Or.inr (Or.inr (Or.inl haj)))
  by_cases hbi : b=i
  · exact four_point_of_index_collision _ (dispersionMatrix_diagonal y z r)
      (dispersionMatrix_skew y z r) a b i j (Or.inr (Or.inr (Or.inr (Or.inl hbi))))
  by_cases hbj : b=j
  · exact four_point_of_index_collision _ (dispersionMatrix_diagonal y z r)
      (dispersionMatrix_skew y z r) a b i j
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hbj)))))
  by_cases hij : i=j
  · exact four_point_of_index_collision _ (dispersionMatrix_diagonal y z r)
      (dispersionMatrix_skew y z r) a b i j
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hij)))))
  exact four_point_physical S (y a) (y b) (y i) (y j)
    (z a) (z b) (z i) (z j) (r a) (r b) (r i) (r j)
    (hy a) (hy b) (hy i) (hy j) (hz a) (hz b) (hz i) (hz j)
    (hcurve a) (hcurve b) (hcurve i) (hcurve j)
    (hden a b hab) (hden a i hai) (hden a j haj)
    (hden b i hbi) (hden b j hbj) (hden i j hij)
    (hroot a) (hroot b) (hroot i) (hroot j)


variable {R ι : Type*} [CommRing R]

/-- Genuine first-row signed-matching recursion, with no division or product shortcut. -/
def indexedPfaffian (K : ι → ι → R) : ℕ → List ι → R
  | 0, _ => 1
  | _+1, [] => 0
  | n+1, a::xs => (xs.zipIdx.map fun (b,j) =>
      (-1 : R)^j * K a b * indexedPfaffian K n (xs.eraseIdx j)).sum

theorem indexedPfaffian_two (K : ι → ι → R) (a b : ι) :
    indexedPfaffian K 1 [a,b] = K a b := by
  simp [indexedPfaffian]

theorem indexedPfaffian_four (K : ι → ι → R) (a b c d : ι) :
    indexedPfaffian K 2 [a,b,c,d] =
      K a b * K c d - K a c * K b d + K a d * K b c := by
  simp [indexedPfaffian]
  ring

/-- Simultaneous row/column scaling, proved for the true matching recursion at every size. -/
theorem indexedPfaffian_diagonal_scale (K : ι → ι → R) (d : ι → R)
    (n : ℕ) (xs : List ι) (hlen : xs.length = 2*n) :
    indexedPfaffian (fun i j => d i*d j*K i j) n xs =
      (xs.map d).prod * indexedPfaffian K n xs := by
  induction n generalizing xs with
  | zero =>
    have hx : xs = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
    subst xs
    simp [indexedPfaffian]
  | succ n ih =>
    cases xs with
    | nil => simp at hlen
    | cons a xs =>
      have hx : xs.length = 2*n+1 := by simp only [List.length_cons] at hlen; omega
      rw [indexedPfaffian, indexedPfaffian, List.map_cons, List.prod_cons,
        ← List.sum_map_mul_left]
      apply congrArg List.sum
      apply List.map_congr_left
      rintro ⟨b,j⟩ hbj
      have hj : j < xs.length := (List.mem_zipIdx' hbj).1
      have hb := (List.mem_zipIdx' hbj).2
      dsimp only
      rw [ih _ (by rw [List.length_eraseIdx_of_lt hj, hx]; omega)]
      have hprod : (xs.map d).prod = d b * ((xs.eraseIdx j).map d).prod := by
        have hh := List.CommMonoid.mul_prod_eraseIdx (l := xs.map d) (i := j) (by simpa using hj)
        simpa only [List.getElem_map, List.eraseIdx_map, hb] using hh.symm
      rw [hprod]
      ring

/-- The four-variable identity is proved for the actual Pfaffian recursion. -/
theorem indexedPfaffian_four_of_relation (K : ι → ι → R) (a b c d : ι)
    (h : K a b * K c d - K a c * K b d + K a d * K b c =
      K a b*K a c*K a d*K b c*K b d*K c d) :
    indexedPfaffian K 2 [a,b,c,d] = K a b*K a c*K a d*K b c*K b d*K c d := by
  rw [indexedPfaffian_four]
  exact h


/-! ## Exact phase of the local amplitude -/

lemma particle_exponent_sum (N : ℕ) : N*(N-1)+N = N^2 := by
  cases N with
  | zero => norm_num
  | succ N => simp; ring

lemma even_square_I_phase (n : ℕ) : (Complex.I : ℂ)^((2*n)^2) = 1 := by
  rw [show (2*n)^2 = 4*(n^2) by ring, pow_mul]
  norm_num

/-- The complex coefficient before combining the kernel and one-body phases. -/
noncomputable def localComplexAmplitude (N : ℕ) (α : ℝ) : ℂ :=
  (2 / ((Nat.factorial N : ℂ) * (2*(Real.pi : ℂ))^(N-1))) *
    (1 / (2*Complex.I*(Real.sin α : ℂ)))^(N*(N-1)) *
    (1 / (Complex.I*(Real.sin α : ℂ)))^N

/-- Exact phase cancellation at even particle orders, with the complete factorial
and constrained Haar normalization preserved. -/
theorem localComplexAmplitude_eq_real (n : ℕ) (α : ℝ) :
    localComplexAmplitude (2*n) α = (localAmplitude (2*n) α : ℂ) := by
  let N := 2*n
  let a : ℂ := Real.sin α
  have hexp := particle_exponent_sum N
  have hphase : (Complex.I : ℂ)^(N^2) = 1 := even_square_I_phase n
  have hden : (2*Complex.I*a)^(N*(N-1)) * (Complex.I*a)^N =
      (2 : ℂ)^(N*(N-1)) * a^(N^2) := by
    calc
      _ = (2 : ℂ)^(N*(N-1)) *
          ((Complex.I*a)^(N*(N-1)) * (Complex.I*a)^N) := by
        rw [show 2*Complex.I*a = 2*(Complex.I*a) by ring, mul_pow]
        ring
      _ = (2 : ℂ)^(N*(N-1)) * (Complex.I*a)^(N*(N-1)+N) := by rw [pow_add]
      _ = _ := by rw [hexp, mul_pow, hphase, one_mul]
  unfold localComplexAmplitude localAmplitude
  change (2 / ((Nat.factorial N : ℂ) * (2*(Real.pi : ℂ))^(N-1))) *
      (1 / (2*Complex.I*a))^(N*(N-1)) * (1 / (Complex.I*a))^N = _
  simp only [one_div, inv_pow]
  rw [mul_assoc, ← mul_inv, hden, mul_inv]
  simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_ofNat,
    Complex.ofReal_natCast, Complex.ofReal_pow, Complex.ofReal_inv, zpow_neg, zpow_natCast]
  dsimp [N, a]
  ring

/-! ## The genuine all-even Pfaffian identity -/

open PfaffianFoundation

theorem recursivePf_diagonal_scale {n : ℕ}
    (A : Matrix (Fin (2*n)) (Fin (2*n)) ℂ) (d : Fin (2*n) → ℂ)
    (hA : ∀ i j, A j i = -A i j) :
    recursivePf n (fun i j => d i * d j * A i j) =
      (∏ i, d i) * recursivePf n A := by
  have heq : (fun i j => d i * d j * A i j) =
      Matrix.diagonal d * A * (Matrix.diagonal d).transpose := by
    ext i j
    simp [Matrix.mul_apply, Matrix.diagonal_apply]
    ring
  rw [heq, recursivePf_congruence A _ hA, Matrix.det_diagonal]

theorem pfPivotBlock_tail_formula {n : ℕ}
    (A : Matrix (Fin (2*(n+1))) (Fin (2*(n+1))) ℂ)
    (hA : ∀ i j, A j i = -A i j) (hp : A 0 1 ≠ 0)
    (i j : Fin (2*n)) :
    (pfPivotShear A * A * (pfPivotShear A).transpose)
        (pfTailIndex n i) (pfTailIndex n j) =
      A (pfTailIndex n i) (pfTailIndex n j) -
        (A 0 (pfTailIndex n i)*A 1 (pfTailIndex n j) -
          A 0 (pfTailIndex n j)*A 1 (pfTailIndex n i)) / A 0 1 := by
  have hmul (i : Fin (2*n)) (x : Fin (2*(n+1))) :
      (pfPivotShear A * A) (pfTailIndex n i) x =
        A 0 x * (A 1 (pfTailIndex n i) / A 0 1) +
          A 1 x * (-A 0 (pfTailIndex n i) / A 0 1) + A (pfTailIndex n i) x := by
    simp only [Matrix.mul_apply]
    simp_rw [mul_comm (pfPivotShear A _ _)]
    exact sum_mul_pfPivotShear_tail A (fun k => A k x) i
  change (∑ x, (pfPivotShear A * A) (pfTailIndex n i) x *
    pfPivotShear A (pfTailIndex n j) x) = _
  rw [sum_mul_pfPivotShear_tail, hmul, hmul, hmul]
  rw [skew_diagonal_zero A hA 0, skew_diagonal_zero A hA 1,
    hA 0 1, hA 0 (pfTailIndex n i), hA 1 (pfTailIndex n i)]
  field_simp
  ring

theorem upperPairProduct_two {n : ℕ}
    (A : Matrix (Fin (2*(n+1))) (Fin (2*(n+1))) ℂ) :
    upperPairProduct A = A 0 1 *
      (∏ i : Fin (2*n), A 0 (pfTailIndex n i)*A 1 (pfTailIndex n i)) *
      upperPairProduct (A.submatrix (pfTailIndex n) (pfTailIndex n)) := by
  change upperPairProduct (N := 2*n+1+1) A = _
  rw [upperPairProduct_succ, upperPairProduct_succ, Fin.prod_univ_succ]
  have heq : (A.submatrix Fin.succ Fin.succ).submatrix Fin.succ Fin.succ =
      A.submatrix (pfTailIndex n) (pfTailIndex n) := by
    ext i j
    change A i.succ.succ j.succ.succ = A (pfTailIndex n i) (pfTailIndex n j)
    rw [pfTailIndex_eq_succ_succ, pfTailIndex_eq_succ_succ]
  rw [heq]
  simp only [Matrix.submatrix_apply, Fin.succ_zero_eq_one, pfTailIndex_eq_succ_succ,
    Finset.prod_mul_distrib]
  simp only [mul_assoc]
  congr 2

theorem recursivePf_product_generic (n : ℕ)
    (A : Matrix (Fin (2*n)) (Fin (2*n)) ℂ)
    (hA : ∀ i j, A j i = -A i j)
    (hnz : ∀ i j, i ≠ j → A i j ≠ 0)
    (hfour : ∀ a b i j,
      A a b*A i j - A a i*A b j + A a j*A b i =
      A a b*A a i*A a j*A b i*A b j*A i j) :
    recursivePf n A = upperPairProduct A := by
  induction n with
  | zero => simp [recursivePf, upperPairProduct]
  | succ n ih =>
    let t := pfTailIndex n
    let D := A.submatrix t t
    let d : Fin (2*n) → ℂ := fun i => A 0 (t i)*A 1 (t i)
    have hp : A 0 1 ≠ 0 := hnz 0 1 (by simp)
    have hD : ∀ i j, D j i = -D i j := fun i j => hA _ _
    have hnzD : ∀ i j, i ≠ j → D i j ≠ 0 := by
      intro i j hij
      apply hnz
      intro he
      apply hij
      apply Fin.ext
      have hh := congrArg Fin.val he
      dsimp [t, pfTailIndex] at hh
      omega
    have hfourD : ∀ a b i j,
        D a b*D i j-D a i*D b j+D a j*D b i =
        D a b*D a i*D a j*D b i*D b j*D i j := fun a b i j => hfour _ _ _ _
    have htail :
        (pfPivotShear A*A*(pfPivotShear A).transpose).submatrix t t =
          fun i j => d i*d j*D i j := by
      ext i j
      change (pfPivotShear A*A*(pfPivotShear A).transpose) (t i) (t j) = _
      rw [pfPivotBlock_tail_formula A hA hp]
      dsimp [d, D, Matrix.submatrix]
      have hf := hfour 0 1 (t i) (t j)
      field_simp
      linear_combination hf
    have hc := recursivePf_congruence A (pfPivotShear A) hA
    rw [pfPivotShear_det, one_mul] at hc
    calc
      recursivePf (n+1) A = recursivePf (n+1)
          (pfPivotShear A*A*(pfPivotShear A).transpose) := hc.symm
      _ = A 0 1 * recursivePf n
          ((pfPivotShear A*A*(pfPivotShear A).transpose).submatrix t t) :=
        recursivePf_pivotBlock A hA hp
      _ = A 0 1*((∏ i, d i)*recursivePf n D) := by
        rw [htail, recursivePf_diagonal_scale D d hD]
      _ = upperPairProduct A := by
        rw [ih D hD hnzD hfourD, upperPairProduct_two]
        simp only [d, D, t, mul_assoc]

theorem recursivePf_zero_of_proportional_rows {n : ℕ}
    (A : Matrix (Fin (2*n)) (Fin (2*n)) ℂ)
    (hA : ∀ i j, A j i = -A i j)
    {a b : Fin (2*n)} (hab : a ≠ b) (t : ℂ) (hrow : A b = t • A a) :
    recursivePf n A = 0 := by
  let E : Matrix (Fin (2*n)) (Fin (2*n)) ℂ := 1
  let P := E.updateRow b (t • E a)
  have hEa : Matrix.vecMul (E a) A = A a := by
    funext j
    change (E*A) a j = A a j
    simp [E]
  have hPA : P*A = A := by
    dsimp [P]
    rw [Matrix.updateRow_mul, Matrix.smul_vecMul, hEa, ← hrow]
    simp [E]
  have hAt : A.transpose = -A := by
    ext i j
    exact hA i j
  have hAP : A*P.transpose = A := by
    have hh := congrArg Matrix.transpose hPA
    rw [Matrix.transpose_mul, hAt, Matrix.neg_mul] at hh
    exact neg_injective hh
  have hdet : P.det = 0 := by
    dsimp [P]
    rw [Matrix.det_updateRow_smul, Matrix.det_updateRow_eq_zero hab, mul_zero]
  have hc := recursivePf_congruence A P hA
  rw [hPA, hAP, hdet, zero_mul] at hc
  exact hc

theorem recursivePf_zero_of_four_point_collision {n : ℕ}
    (A : Matrix (Fin (2*n)) (Fin (2*n)) ℂ)
    (hA : ∀ i j, A j i = -A i j)
    {a b : Fin (2*n)} (hab : a ≠ b) (hz : A a b = 0)
    (hfour : ∀ i j,
      A a b*A i j - A a i*A b j + A a j*A b i =
      A a b*A a i*A a j*A b i*A b j*A i j) :
    recursivePf n A = 0 := by
  by_cases hrow0 : ∀ i, A a i = 0
  · apply recursivePf_zero_of_proportional_rows A hA hab.symm 0
    ext i
    simp [hrow0]
  · push Not at hrow0
    obtain ⟨c, hc⟩ := hrow0
    let t := A b c / A a c
    have hrow : A b = t • A a := by
      ext j
      change A b j = (A b c / A a c)*A a j
      have hh := hfour c j
      rw [hz] at hh
      field_simp
      linear_combination -hh
    exact recursivePf_zero_of_proportional_rows A hA hab t hrow

theorem upperPairProduct_zero_of_pair {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℂ)
    (hA : ∀ i j, A j i = -A i j)
    {a b : Fin N} (hab : a ≠ b) (hz : A a b = 0) :
    upperPairProduct A = 0 := by
  unfold upperPairProduct
  rcases lt_or_gt_of_ne hab with hab | hab
  · apply Finset.prod_eq_zero (Finset.mem_univ a)
    exact Finset.prod_eq_zero (Finset.mem_Ioi.mpr hab) hz
  · apply Finset.prod_eq_zero (Finset.mem_univ b)
    apply Finset.prod_eq_zero (Finset.mem_Ioi.mpr hab)
    rw [hA, hz, neg_zero]

theorem recursivePf_product (n : ℕ)
    (A : Matrix (Fin (2*n)) (Fin (2*n)) ℂ)
    (hA : ∀ i j, A j i = -A i j)
    (hfour : ∀ a b i j,
      A a b*A i j - A a i*A b j + A a j*A b i =
      A a b*A a i*A a j*A b i*A b j*A i j) :
    recursivePf n A = upperPairProduct A := by
  by_cases hnz : ∀ i j, i ≠ j → A i j ≠ 0
  · exact recursivePf_product_generic n A hA hnz hfour
  · push Not at hnz
    obtain ⟨a, b, hab, hz⟩ := hnz
    rw [recursivePf_zero_of_four_point_collision A hA hab hz (hfour a b),
      upperPairProduct_zero_of_pair A hA hab hz]

/-- Proposition 4.3 for the actual first-row recursive Pfaffian, at every even
particle order and all zero-pair loci on the common dispersion curve. -/
theorem dispersion_pfaffian_product (n : ℕ) (S : ℂ)
    (y z r : Fin (2*n) → ℂ)
    (hy : ∀ i, y i ≠ 0) (hz : ∀ i, z i ≠ 0)
    (hcurve : ∀ i, y i + (y i)⁻¹ + z i + (z i)⁻¹ = 2*S)
    (hden : ∀ i j, i ≠ j → 1-z i*z j ≠ 0)
    (hroot : ∀ i, r i^2 = z i / y i) :
    recursivePf n (dispersionMatrix y z r) =
      ∏ i, ∏ j ∈ Finset.Ioi i, dispersionMatrix y z r i j := by
  apply recursivePf_product n (dispersionMatrix y z r)
    (fun i j => dispersionMatrix_skew y z r j i)
  intro a b i j
  by_cases hc : a=b ∨ a=i ∨ a=j ∨ b=i ∨ b=j ∨ i=j
  · exact four_point_of_index_collision _ (dispersionMatrix_diagonal y z r)
      (dispersionMatrix_skew y z r) a b i j hc
  push Not at hc
  obtain ⟨hab, hai, haj, hbi, hbj, hij⟩ := hc
  exact four_point_physical S (y a) (y b) (y i) (y j)
    (z a) (z b) (z i) (z j) (r a) (r b) (r i) (r j)
    (hy a) (hy b) (hy i) (hy j) (hz a) (hz b) (hz i) (hz j)
    (hcurve a) (hcurve b) (hcurve i) (hcurve j)
    (hden a b hab) (hden a i hai) (hden a j haj)
    (hden b i hbi) (hden b j hbj) (hden i j hij)
    (hroot a) (hroot b) (hroot i) (hroot j)

end IsingBulk.Preferred22
