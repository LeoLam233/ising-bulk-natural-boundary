import IsingBulk.AnisoF002.Isotropic.BalancedContour
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# F002: differentiating the actual balanced occupancy

The whole complex balanced contour is differentiated before any smooth
partition is inserted.  Both derivatives of the global bump populations
are retained.  This proves the exact rank-two correction in F002's
occupancy derivative, not the later coarea or integrability estimate.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- A differentiable real path in the full balanced complex contour. -/
def balancedContourPath (scale : ℝ) (θ p m : ι → ℝ → ℝ) (t : ℝ) (i : ι) : ℂ :=
  contourCoordinate (fun j => θ j t)
    (balancedShift scale (fun j => p j t) (fun j => m j t)) i

/-- The full derivative of the real displacement includes both population derivatives. -/
theorem balancedShift_hasDerivAt (scale x : ℝ) (p m : ι → ℝ → ℝ)
    (p' m' : ι → ℝ) (hp : ∀ i, HasDerivAt (p i) (p' i) x)
    (hm : ∀ i, HasDerivAt (m i) (m' i) x) (i : ι) :
    HasDerivAt
      (fun t => balancedShift scale (fun j => p j t) (fun j => m j t) i)
      (scale * ((∑ j, p' j) * m i x + (∑ j, p j x) * m' i -
        ((∑ j, m' j) * p i x + (∑ j, m j x) * p' i))) x := by
  have hP : HasDerivAt (fun t => ∑ j, p j t) (∑ j, p' j) x :=
    HasDerivAt.fun_sum fun j _ => hp j
  have hQ : HasDerivAt (fun t => ∑ j, m j t) (∑ j, m' j) x :=
    HasDerivAt.fun_sum fun j _ => hm j
  exact ((hP.mul (hm i)).sub (hQ.mul (hp i))).const_mul scale

/-- The actual complex path derivative, with no frozen-population approximation. -/
theorem balancedContourPath_hasDerivAt (scale x : ℝ) (θ p m : ι → ℝ → ℝ)
    (a p' m' : ι → ℝ) (hθ : ∀ i, HasDerivAt (θ i) (a i) x)
    (hp : ∀ i, HasDerivAt (p i) (p' i) x)
    (hm : ∀ i, HasDerivAt (m i) (m' i) x) (i : ι) :
    HasDerivAt (fun t => balancedContourPath scale θ p m t i)
      ((a i : ℂ) - Complex.I *
        ((scale * ((∑ j, p' j) * m i x + (∑ j, p j x) * m' i -
          ((∑ j, m' j) * p i x + (∑ j, m j x) * p' i)) : ℝ) : ℂ)) x := by
  exact (hθ i).ofReal_comp.sub
    ((balancedShift_hasDerivAt scale x p m p' m' hp hm i).ofReal_comp.const_mul Complex.I)

/-- Chain rule on every coordinate followed by the exact finite sum rule. -/
theorem occupancy_path_hasDerivAt (scale x : ℝ) (θ p m : ι → ℝ → ℝ)
    (a p' m' : ι → ℝ) (φ : ℂ → ℂ) (φ' : ι → ℂ)
    (hθ : ∀ i, HasDerivAt (θ i) (a i) x)
    (hp : ∀ i, HasDerivAt (p i) (p' i) x)
    (hm : ∀ i, HasDerivAt (m i) (m' i) x)
    (hφ : ∀ i, HasDerivAt φ (φ' i) (balancedContourPath scale θ p m x i)) :
    HasDerivAt (fun t => ∑ i, φ (balancedContourPath scale θ p m t i))
      (∑ i, φ' i * ((a i : ℂ) - Complex.I *
        ((scale * ((∑ j, p' j) * m i x + (∑ j, p j x) * m' i -
          ((∑ j, m' j) * p i x + (∑ j, m j x) * p' i)) : ℝ) : ℂ))) x := by
  apply HasDerivAt.fun_sum
  intro i _
  have hc := (hφ i).comp x (balancedContourPath_hasDerivAt scale x θ p m a p' m' hθ hp hm i)
  simpa only [Function.comp_apply] using! hc

/-- Vary exactly one original real angle in the full torus. -/
def coordinateLine [DecidableEq ι] (θ : ι → ℝ) (i : ι) (t : ℝ) (j : ι) : ℝ :=
  if j = i then θ i + t else θ j

omit [Fintype ι] in
@[simp] theorem coordinateLine_zero [DecidableEq ι] (θ : ι → ℝ) (i j : ι) :
    coordinateLine θ i 0 j = θ j := by
  by_cases h : j = i
  · subst j
    simp [coordinateLine]
  · simp [coordinateLine, h]

omit [Fintype ι] in
theorem coordinateLine_hasDerivAt [DecidableEq ι] (θ : ι → ℝ) (i j : ι) :
    HasDerivAt (fun t => coordinateLine θ i t j) (if j = i then 1 else 0) 0 := by
  by_cases h : j = i
  · subst j
    simpa only [coordinateLine, ite_true, zero_add] using!
      (hasDerivAt_const (0 : ℝ) (θ i)).add (hasDerivAt_id (0 : ℝ))
  · simpa only [coordinateLine, h, ite_false] using
      (hasDerivAt_const (0 : ℝ) (θ j))

omit [Fintype ι] in
theorem bump_coordinateLine_hasDerivAt [DecidableEq ι]
    (θ : ι → ℝ) (i j : ι) (p : ℝ → ℝ) (p' : ℝ)
    (hp : HasDerivAt p p' (θ i)) :
    HasDerivAt (fun t => p (coordinateLine θ i t j)) (if j = i then p' else 0) 0 := by
  by_cases h : j = i
  · subst j
    have hline := coordinateLine_hasDerivAt θ i i
    simpa only [coordinateLine_zero, ite_true, mul_one, Function.comp_apply] using! hp.comp_of_eq 0 hline (coordinateLine_zero θ i i).symm
  · simpa only [coordinateLine, h, ite_false] using
      (hasDerivAt_const (0 : ℝ) (p (θ j)))

/-- The exact deformed occupancy, before any partition or chart pullback. -/
def deformedOccupancy [DecidableEq ι] (scale : ℝ) (θ : ι → ℝ) (i : ι)
    (p m : ℝ → ℝ) (φ : ℂ → ℂ) (t : ℝ) : ℂ :=
  ∑ j, φ (balancedContourPath scale (fun j t => coordinateLine θ i t j)
    (fun j t => p (coordinateLine θ i t j))
    (fun j t => m (coordinateLine θ i t j)) t j)

/-- Regrouping the complete differentiated sum produces the exact two global terms. -/
theorem occupancy_rank_two_identity [DecidableEq ι]
    (scale p' m' : ℝ) (p m : ι → ℝ) (φ' : ι → ℂ) (i : ι) :
    (∑ j, φ' j * (((if j = i then 1 else 0 : ℝ) : ℂ) - Complex.I *
      ((scale * (p' * m j + (∑ l, p l) * (if j = i then m' else 0) -
        (m' * p j + (∑ l, m l) * (if j = i then p' else 0))) : ℝ) : ℂ))) =
      φ' i * (1 - Complex.I * (scale : ℂ) *
        (((∑ l, p l : ℝ) : ℂ) * (m' : ℂ) - ((∑ l, m l : ℝ) : ℂ) * (p' : ℂ))) -
      Complex.I * (scale : ℂ) * (p' : ℂ) * (∑ j, (m j : ℂ) * φ' j) +
      Complex.I * (scale : ℂ) * (m' : ℂ) * (∑ j, (p j : ℂ) * φ' j) := by
  have hterm : ∀ j, φ' j * (((if j = i then 1 else 0 : ℝ) : ℂ) - Complex.I *
      ((scale * (p' * m j + (∑ l, p l) * (if j = i then m' else 0) -
        (m' * p j + (∑ l, m l) * (if j = i then p' else 0))) : ℝ) : ℂ)) =
      (if j = i then φ' i * (1 - Complex.I * (scale : ℂ) *
        (((∑ l, p l : ℝ) : ℂ) * (m' : ℂ) - ((∑ l, m l : ℝ) : ℂ) * (p' : ℂ))) else 0) -
      Complex.I * (scale : ℂ) * (p' : ℂ) * ((m j : ℂ) * φ' j) +
      Complex.I * (scale : ℂ) * (m' : ℂ) * ((p j : ℂ) * φ' j) := by
    intro j
    by_cases h : j = i
    · subst j
      simp only [ite_true, Complex.ofReal_one, Complex.ofReal_mul, Complex.ofReal_add,
        Complex.ofReal_sub]
      ring
    · simp only [h, ite_false, Complex.ofReal_zero, Complex.ofReal_mul, Complex.ofReal_add,
        Complex.ofReal_sub]
      ring
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, ← Finset.mul_sum]

/-- The actual coordinate derivative in F002, including the rank-two population
correction.  `scale = τ/N`; the two local coefficients are therefore `τρ` and `τυ`. -/
theorem deformedOccupancy_hasDerivAt [DecidableEq ι]
    (scale : ℝ) (θ : ι → ℝ) (i : ι) (p m : ℝ → ℝ) (p' m' : ℝ)
    (φ : ℂ → ℂ) (φ' : ι → ℂ)
    (hp : HasDerivAt p p' (θ i)) (hm : HasDerivAt m m' (θ i))
    (hφ : ∀ j, HasDerivAt φ (φ' j)
      (contourCoordinate θ (balancedShift scale (fun l => p (θ l)) (fun l => m (θ l))) j)) :
    HasDerivAt (deformedOccupancy scale θ i p m φ)
      (φ' i * (1 - Complex.I * (scale : ℂ) *
        (((∑ l, p (θ l) : ℝ) : ℂ) * (m' : ℂ) -
          ((∑ l, m (θ l) : ℝ) : ℂ) * (p' : ℂ))) -
        Complex.I * (scale : ℂ) * (p' : ℂ) * (∑ j, (m (θ j) : ℂ) * φ' j) +
        Complex.I * (scale : ℂ) * (m' : ℂ) * (∑ j, (p (θ j) : ℂ) * φ' j)) 0 := by
  have h := occupancy_path_hasDerivAt scale 0
    (fun j t => coordinateLine θ i t j)
    (fun j t => p (coordinateLine θ i t j))
    (fun j t => m (coordinateLine θ i t j))
    (fun j => if j = i then 1 else 0)
    (fun j => if j = i then p' else 0)
    (fun j => if j = i then m' else 0) φ φ'
    (fun j => coordinateLine_hasDerivAt θ i j)
    (fun j => bump_coordinateLine_hasDerivAt θ i j p p' hp)
    (fun j => bump_coordinateLine_hasDerivAt θ i j m m' hm)
    (fun j => by simpa only [balancedContourPath, coordinateLine_zero] using hφ j)
  simp only [coordinateLine_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h
  rw [occupancy_rank_two_identity] at h
  exact h

end IsingBulk.AnisoF002.Isotropic
