import IsingBulk.AnisoF002.C03.RegularPhaseDifferential
import IsingBulk.AnisoF002.C03.IsotropicTrigonometricSecants

/-!
# The actual regular-edge numerator through every collision divisor

The filled quotient uses the entire sinc, and therefore never divides by
the Vandermonde.  The exact factorization holds at partial coincidences as
well as at the total collision.  Its nonzero center retains every one-body,
pair and anisotropy factor of the original complete numerator.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open Set Filter IsingBulk.AnisoF002.Isotropic
open scoped Topology BigOperators

def edgeVandermondeSquared {N : ℕ} (x : Fin N → ℂ) : ℂ :=
  ∏ ij ∈ indexPairs N, (x ij.1 - x ij.2) ^ 2

def edgeCollisionNumerator {N : ℕ} (c a : ℂ → ℂ) (p : ℂ × (Fin N → ℂ)) : ℂ :=
  edgePrefactor a p.1 ^ N *
    (∏ i, edgeOneBody c a (p.1, Complex.cos (p.2 i))) *
    ∏ ij ∈ indexPairs N,
      edgeSineCoefficient c a (p.1, Complex.cos (p.2 ij.1), Complex.cos (p.2 ij.2)) *
        (complexSinc ((p.2 ij.1 - p.2 ij.2) / 2) / 2) ^ 2

theorem sine_squared_collision_factorization (x y : ℂ) :
    Complex.sin ((x - y) / 2) ^ 2 =
      (x - y) ^ 2 * (complexSinc ((x - y) / 2) / 2) ^ 2 := by
  rw [← complexSinc_mul ((x - y) / 2)]
  ring

theorem edgeJointNumerator_collision_factorization {N : ℕ} (c a : ℂ → ℂ)
    (p : ℂ × (Fin N → ℂ)) :
    edgeJointNumerator c a p = edgeVandermondeSquared p.2 * edgeCollisionNumerator c a p := by
  unfold edgeJointNumerator edgeCollisionNumerator edgeVandermondeSquared
  have hp (ij : Fin N × Fin N) :
      edgeSineCoefficient c a (p.1, Complex.cos (p.2 ij.1), Complex.cos (p.2 ij.2)) *
        Complex.sin ((p.2 ij.1 - p.2 ij.2) / 2) ^ 2 =
      (p.2 ij.1 - p.2 ij.2) ^ 2 *
        (edgeSineCoefficient c a (p.1, Complex.cos (p.2 ij.1), Complex.cos (p.2 ij.2)) *
          (complexSinc ((p.2 ij.1 - p.2 ij.2) / 2) / 2) ^ 2) := by
    rw [sine_squared_collision_factorization]
    ring
  simp_rw [hp]
  rw [Finset.prod_mul_distrib]
  ring

theorem edgeFullNumerator_collision_factorization {N : ℕ} (c a : ℂ → ℂ)
    (t : ℂ) (x : Fin N → ℝ) :
    edgeFullNumerator c a t x =
      edgeVandermondeSquared (complexAngles x) * edgeCollisionNumerator c a (t, complexAngles x) := by
  rw [← edgeJointNumerator_real, edgeJointNumerator_collision_factorization]

theorem edgeCollisionNumerator_center {N : ℕ} (b : ℝ) (a : ℂ → ℂ) :
    edgeCollisionNumerator (affineEdgeCenter b) a ((0 : ℂ), (0 : Fin N → ℂ)) =
      edgePrefactor a 0 ^ N *
        (2 * upperEdgeRoot (b : ℂ) / (1 - upperEdgeRoot (b : ℂ) ^ 2)) ^ N *
        (sinePairCoefficient (a 0) (upperEdgeRoot (b : ℂ)) (upperEdgeRoot (b : ℂ)) /
          4) ^ (N.choose 2) := by
  simp only [edgeCollisionNumerator, Pi.zero_apply, Complex.cos_zero, sub_self,
    zero_div, complexSinc_zero, edgeOneBody, edgeSineCoefficient, edgeJointRoot,
    affineEdgeCenter, add_zero, sub_self, mul_zero, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, card_indexPairs]
  congr 1
  congr 1
  ring

theorem edgeCollisionNumerator_center_ne_zero {N : ℕ} {b : ℝ} {a : ℂ → ℂ}
    (hb : |b| < 1) (ha : a 0 ≠ 0) :
    edgeCollisionNumerator (affineEdgeCenter b) a ((0 : ℂ), (0 : Fin N → ℂ)) ≠ 0 := by
  have hr := upperEdgeRoot_ne_zero (b : ℂ)
  have hreg : upperEdgeRegion (b : ℂ) := Or.inr ⟨rfl, hb⟩
  have hd := upperEdgeRoot_pair_denominator hreg hreg
  have hd' : 1 - upperEdgeRoot (b : ℂ) ^ 2 ≠ 0 := by simpa only [pow_two] using hd
  have hp : edgePrefactor a 0 ≠ 0 := by
    intro he
    have hh := edgePrefactor_sq a 0
    rw [he, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hh
    exact ha hh.symm
  rw [edgeCollisionNumerator_center]
  refine mul_ne_zero (mul_ne_zero (pow_ne_zero _ hp)
    (pow_ne_zero _ (div_ne_zero (mul_ne_zero (by norm_num) hr) hd'))) ?_
  apply pow_ne_zero
  apply div_ne_zero _ (by norm_num)
  exact div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) ha) hr) hr)
    (pow_ne_zero _ hd)

namespace RegularEdgeControl
variable {c a : ℂ → ℂ} (d : RegularEdgeControl c a)

theorem collisionNumerator_analytic {N : ℕ} {p : ℂ × (Fin N → ℂ)}
    (ht : p.1 ∈ Metric.closedBall (0 : ℂ) d.radius)
    (hx : ∀ i, Complex.cos (p.2 i) ∈ Metric.thickening d.cosineRadius complexCosineInterval) :
    AnalyticAt ℂ (edgeCollisionNumerator c a) p := by
  have hc (i : Fin N) : AnalyticAt ℂ (fun q : ℂ × (Fin N → ℂ) => Complex.cos (q.2 i)) p :=
    Complex.analyticAt_cos.comp (analyticAt_angle_coordinate i p)
  have hone (i : Fin N) : AnalyticAt ℂ
      (fun q : ℂ × (Fin N → ℂ) => edgeOneBody c a (q.1, Complex.cos (q.2 i))) p := by
    have hprot := d.protected_pairs p.1 ht _ (hx i) _ (hx i)
    exact (edgeOneBody_analyticAt hprot.1 hprot.2.2.1).comp
      (f := fun q : ℂ × (Fin N → ℂ) => (q.1, Complex.cos (q.2 i)))
      (analyticAt_fst.prod (hc i))
  have hpair (ij : Fin N × Fin N) : AnalyticAt ℂ
      (fun q : ℂ × (Fin N → ℂ) =>
        edgeSineCoefficient c a (q.1, Complex.cos (q.2 ij.1), Complex.cos (q.2 ij.2)) *
          (complexSinc ((q.2 ij.1 - q.2 ij.2) / 2) / 2) ^ 2) p := by
    have hs := edgeSineCoefficient_analyticAt (d.coefficient_analytic p.1 ht)
      (d.protected_pairs p.1 ht _ (hx ij.1) _ (hx ij.2))
    exact (hs.comp
      (f := fun q : ℂ × (Fin N → ℂ) => (q.1, Complex.cos (q.2 ij.1), Complex.cos (q.2 ij.2)))
      (analyticAt_fst.prod ((hc ij.1).prod (hc ij.2)))).mul
      ((((complexSinc_analyticAt _).comp (((analyticAt_angle_coordinate ij.1 p).sub
        (analyticAt_angle_coordinate ij.2 p)).div_const)).div_const).pow 2)
  exact (((d.prefactor_analytic p.1 ht).comp analyticAt_fst).pow N).mul
    (Finset.univ.analyticAt_fun_prod fun i _ => hone i) |>.mul
      ((indexPairs N).analyticAt_fun_prod fun ij _ => hpair ij)

end RegularEdgeControl

theorem collisionNumerator_nonzero_germ {N : ℕ} {b : ℝ} {a : ℂ → ℂ}
    (d : RegularEdgeControl (affineEdgeCenter b) a) (hb : |b| < 1) (ha : a 0 ≠ 0) :
    ∀ᶠ p : ℂ × (Fin N → ℂ) in 𝓝 (0, 0),
      AnalyticAt ℂ (edgeCollisionNumerator (affineEdgeCenter b) a) p ∧
        edgeCollisionNumerator (affineEdgeCenter b) a p ≠ 0 := by
  have han : AnalyticAt ℂ (edgeCollisionNumerator (affineEdgeCenter b) a)
      ((0 : ℂ), (0 : Fin N → ℂ)) := by
    apply d.collisionNumerator_analytic (Metric.mem_closedBall_self d.radius_pos.le)
    intro i
    simp only [Pi.zero_apply, Complex.cos_zero]
    exact Metric.self_subset_thickening d.cosineRadius_pos _
      (by refine ⟨1, by norm_num, by simp⟩)
  exact han.eventually_analyticAt.and
    (han.continuousAt.eventually_ne (edgeCollisionNumerator_center_ne_zero hb ha))

end
end IsingBulk.AnisoF002.RegularTail.C03
