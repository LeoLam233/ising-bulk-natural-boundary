import Mathlib.Analysis.RCLike.Sqrt
import Mathlib.Tactic

/-! Exact finite-dimensional algebra of ANISO §4.3–4.4.
The quadratic form here is complex bilinear, not the Hermitian norm.
No identity in this file divides by that quadratic form. -/
namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open scoped BigOperators

abbrev Config (n : ℕ) := Fin n → ℂ

def pairing {n : ℕ} (v w : Config n) : ℂ := ∑ i, v i * w i

def quadratic {n : ℕ} (v : Config n) : ℂ := ∑ i, v i ^ 2

def mean {n : ℕ} (v : Config n) : ℂ := (∑ i, v i) / n

def project {n : ℕ} (v : Config n) : Config n := fun i => v i - mean v

def ZeroMean {n : ℕ} (v : Config n) : Prop := ∑ i, v i = 0

@[simp] theorem pairing_self {n : ℕ} (v : Config n) : pairing v v = quadratic v := by
  simp [pairing, quadratic, pow_two]

theorem project_difference {n : ℕ} (v : Config n) (i j : Fin n) :
    project v i - project v j = v i - v j := by simp [project]

theorem project_zeroMean {n : ℕ} (hn : n ≠ 0) (v : Config n) : ZeroMean (project v) := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  simp only [ZeroMean, project, mean, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

theorem quadratic_add {n : ℕ} (v w : Config n) (c : ℂ) :
    quadratic (fun i => v i + c * w i) =
      quadratic v + 2 * c * pairing v w + c ^ 2 * quadratic w := by
  unfold quadratic pairing
  simp_rw [show ∀ i : Fin n, (v i + c * w i)^2 =
      v i ^ 2 + 2*c*(v i*w i) + c^2*w i^2 by intro i; ring]
  simp [Finset.sum_add_distrib, Finset.mul_sum]

theorem quadratic_scale {n : ℕ} (v : Config n) (c : ℂ) :
    quadratic (fun i => c * v i) = c ^ 2 * quadratic v := by
  simp [quadratic, mul_pow, Finset.mul_sum]

theorem quadratic_project {n : ℕ} (hn : n ≠ 0) (v : Config n) :
    quadratic (project v) + n * mean v ^ 2 = quadratic v := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hsum : ∑ i, v i = (n : ℂ) * mean v := by
    unfold mean
    field_simp
  have he : quadratic (project v) = quadratic v - 2 * mean v * (∑ i, v i) +
      n * mean v ^ 2 := by
    unfold quadratic project
    simp_rw [show ∀ i : Fin n, (v i - mean v)^2 =
      v i ^ 2 - 2 * mean v * v i + mean v ^ 2 by intro i; ring]
    simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
  rw [he, hsum]
  ring

/-- Equation (4.32), using the principal square root, which is analytic near one. -/
def rankOneCoefficient {n : ℕ} (ell : Config n) : ℂ :=
  n / (1 + Complex.sqrt (1 + n * quadratic ell))

/-- Equation (4.31) with the Hadamard pairing substituted for the mean. -/
def meanCorrection {n : ℕ} (ell w : Config n) : Config n :=
  fun i => w i + rankOneCoefficient ell * pairing w ell * ell i

theorem sqrt_sq (z : ℂ) : Complex.sqrt z ^ 2 = z := by
  exact Complex.cpow_nat_inv_pow z (n := 2) (by decide)

theorem one_add_sqrt_ne_zero (z : ℂ) : 1 + Complex.sqrt z ≠ 0 := by
  intro h
  have hr := congrArg Complex.re h
  have hp : 0 ≤ (Complex.sqrt z).re := by
    change 0 ≤ (z ^ (2⁻¹ : ℂ)).re
    rw [Complex.cpow_inv_two_re]
    positivity
  simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at hr
  linarith

theorem rankOneCoefficient_identity {n : ℕ} (ell : Config n) :
    2 * rankOneCoefficient ell + rankOneCoefficient ell ^ 2 * quadratic ell = n := by
  have hs := sqrt_sq (1 + (n : ℂ) * quadratic ell)
  have hd := one_add_sqrt_ne_zero (1 + (n : ℂ) * quadratic ell)
  unfold rankOneCoefficient
  field_simp
  linear_combination -(n : ℂ) * hs

/-- The exact mean correction, valid also when `quadratic w = 0`. -/
theorem quadratic_meanCorrection {n : ℕ} (ell w : Config n) :
    quadratic (meanCorrection ell w) = quadratic w + n * pairing w ell ^ 2 := by
  unfold meanCorrection
  rw [quadratic_add]
  have h := rankOneCoefficient_identity ell
  linear_combination pairing w ell ^ 2 * h

theorem meanCorrection_zeroMean {n : ℕ} (ell w : Config n)
    (he : ZeroMean ell) (hw : ZeroMean w) : ZeroMean (meanCorrection ell w) := by
  simp only [ZeroMean, meanCorrection, Finset.sum_add_distrib, ← Finset.mul_sum] at *
  rw [he, hw]
  ring

theorem meanCorrection_difference {n : ℕ} (ell w : Config n) (i j : Fin n) :
    meanCorrection ell w i - meanCorrection ell w j =
      (w i - w j) + rankOneCoefficient ell * pairing w ell * (ell i - ell j) := by
  simp only [meanCorrection]
  ring

/-- The pairwise correction factor, with no division by a coincidence divisor. -/
theorem meanCorrection_difference_factor {n : ℕ} (ell w : Config n) (i j : Fin n)
    (L : ℂ) (hL : ell i - ell j = (w i - w j) * L) :
    meanCorrection ell w i - meanCorrection ell w j =
      (w i - w j) * (1 + rankOneCoefficient ell * pairing w ell * L) := by
  rw [meanCorrection_difference, hL]
  ring

/-- Algebraic heart of (4.33). The hypothesis is the Hadamard identity,
not a normal-form or an estimate hypothesis. -/
theorem meanCorrection_recovers_energy {n : ℕ} (hn : n ≠ 0) (u ell : Config n)
    (hmean : pairing (project u) ell = mean u) :
    quadratic (meanCorrection ell (project u)) = quadratic u := by
  rw [quadratic_meanCorrection, hmean]
  exact quadratic_project hn u

/-- Exact identity including the scalar `sqrt h` in (4.34). -/
theorem scaled_meanCorrection_recovers_energy {n : ℕ} (hn : n ≠ 0)
    (u ell : Config n) (h : ℂ) (hmean : pairing (project u) ell = mean u) :
    quadratic (fun i => Complex.sqrt h * meanCorrection ell (project u) i) =
      h * quadratic u := by
  rw [quadratic_scale, sqrt_sq, meanCorrection_recovers_energy hn u ell hmean]

/-- Bilinear transpose pairing for the rank-one transformation. -/
theorem pairing_meanCorrection {n : ℕ} (ell w : Config n) :
    pairing (meanCorrection ell w) ell =
      (1 + rankOneCoefficient ell * quadratic ell) * pairing w ell := by
  unfold pairing meanCorrection quadratic
  simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum, pow_two]
  simp only [pairing]
  ring

/-- The transformation is an actual square root of `I + n ell ellᵀ`,
not merely an energy-preserving surrogate. -/
theorem meanCorrection_twice {n : ℕ} (ell w : Config n) :
    meanCorrection ell (meanCorrection ell w) =
      fun i => w i + n * pairing w ell * ell i := by
  funext i
  change meanCorrection ell w i + rankOneCoefficient ell *
    pairing (meanCorrection ell w) ell * ell i = _
  rw [pairing_meanCorrection]
  simp only [meanCorrection]
  linear_combination pairing w ell * ell i * rankOneCoefficient_identity ell

/-- An actual nonzero complex null-cone point in the three-particle zero-mean plane. -/
def nullConeWitness : Config 3 :=
  ![1, (-1 + Complex.sqrt (-3)) / 2, (-1 - Complex.sqrt (-3)) / 2]

theorem nullConeWitness_zeroMean : ZeroMean nullConeWitness := by
  unfold ZeroMean
  rw [Fin.sum_univ_three]
  change 1 + (-1 + Complex.sqrt (-3)) / 2 + (-1 - Complex.sqrt (-3)) / 2 = 0
  ring

theorem nullConeWitness_quadratic : quadratic nullConeWitness = 0 := by
  unfold quadratic
  rw [Fin.sum_univ_three]
  change 1^2 + ((-1 + Complex.sqrt (-3)) / 2)^2 + ((-1 - Complex.sqrt (-3)) / 2)^2 = 0
  have hs := sqrt_sq (-3)
  linear_combination hs / 2

theorem nullConeWitness_ne_zero : nullConeWitness ≠ 0 := by
  intro h
  have hh := congrFun h 0
  norm_num [nullConeWitness] at hh

end
end IsingBulk.Anisotropic.NegativeNormalForm
