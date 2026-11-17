import IsingBulk.AnisoF002.Isotropic.AnalyticSecants
import IsingBulk.AnisoF002.Isotropic.VarianceCoercivity
import IsingBulk.AnisoF002.Isotropic.BalancedJacobian
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# The covariance field of the actual compatible right inverse

Frozen/public F002 `eq:iso-covariance-field` and the two transport
constraints following it.  The inverse, its joint domain, its first and
second secants, and its parameter derivatives are actual functions.
The one joint neighborhood is chosen before every particle number.

The variance hypothesis on a general complex tuple is explicit.  It is
discharged below on every nonconstant real right-arc tuple.  Extension to
all physical deformed images, the protected polynomial jet estimates,
and the full scalar Piola current are not asserted here.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators
open Set Metric

def rightInverseSliceDomain (S₀ r : ℝ) (S : ℂ) : Set ℂ :=
  {z | (S, z) ∈ thickening r (rightParameterSegment S₀)}

theorem rightInverseSliceDomain_convex (S₀ r : ℝ) (S : ℂ) :
    Convex ℝ (rightInverseSliceDomain S₀ r S) := by
  have h := (rightParameterSegment_convex S₀).thickening r
  intro x hx y hy a b ha hb hab
  have hh := h hx hy ha hb hab
  simpa only [rightInverseSliceDomain, mem_ofPred_eq, Prod.smul_mk,
    Prod.mk_add_mk, ← add_smul, hab, one_smul] using hh

theorem analytic_joint_affine_path_hasDerivAt (U : ℂ × ℂ → ℂ) (S v B : ℂ)
    (hU : AnalyticAt ℂ U (S, v)) :
    HasDerivAt (fun t : ℂ => U (S + t, v + t * B))
      (deriv (fun z => U (z, v)) S + deriv (fun z => U (S, z)) v * B) 0 := by
  let L := fderiv ℂ U (S, v)
  have hUS : deriv (fun z => U (z, v)) S = L (1, 0) := by
    exact (hU.differentiableAt.hasFDerivAt.comp_hasDerivAt S
      (HasDerivAt.prodMk (hasDerivAt_id S) (hasDerivAt_const S v))).deriv
  have hUv : deriv (fun z => U (S, z)) v = L (0, 1) := by
    exact (hU.differentiableAt.hasFDerivAt.comp_hasDerivAt v
      (HasDerivAt.prodMk (hasDerivAt_const v S) (hasDerivAt_id v))).deriv
  have hpath : HasDerivAt (fun t : ℂ => (S + t, v + t * B)) (1, B) 0 := by
    simpa only [one_mul, id_eq] using!
      ((hasDerivAt_id (0 : ℂ)).const_add S).prodMk
        (((hasDerivAt_id (0 : ℂ)).mul_const B).const_add v)
  have hU' : HasFDerivAt U L (S + 0, v + 0 * B) := by
    simpa only [add_zero, zero_mul] using hU.differentiableAt.hasFDerivAt
  have h := hU'.comp_hasDerivAt 0 hpath
  have hid : (1, B) = (1, 0) + B • ((0, 1) : ℂ × ℂ) := by ext <;> simp
  have hL : L (1, B) = deriv (fun z => U (z, v)) S +
      deriv (fun z => U (S, z)) v * B := by
    rw [hid, map_add, map_smul, ← hUS, ← hUv, smul_eq_mul, mul_comm B]
  exact h.congr_deriv hL

variable {ι : Type*} [Fintype ι]

def rightCovarianceAmplitude (S : ℂ) (v : ι → ℂ) : ℂ :=
  -∑ i, deriv (fun z => explicitRightInverse (z, v i)) S

def rightCovarianceField (S : ℂ) (v : ι → ℂ) (i : ι) : ℂ :=
  analyticCovarianceField (rightCovarianceAmplitude S v)
    (fun z => explicitRightInverse (S, z)) v i

theorem rightCovarianceField_sum (S : ℂ) (v : ι → ℂ) :
    ∑ i, rightCovarianceField S v i = 0 :=
  analyticCovarianceField_sum _ _ _

/-- A direct chain-rule statement for the actual total phase, with the
actual parameter derivative and the actual coordinate velocity. -/
theorem rightCovarianceField_phase_derivative (S : ℂ) (v : ι → ℂ)
    (hU : ∀ i, AnalyticAt ℂ explicitRightInverse (S, v i))
    (htransport : (∑ i, deriv (fun z => explicitRightInverse (S, z)) (v i) *
      rightCovarianceField S v i) = rightCovarianceAmplitude S v) :
    HasDerivAt (fun t : ℂ => ∑ i,
      ((v i + t * rightCovarianceField S v i) -
        explicitRightInverse (S + t, v i + t * rightCovarianceField S v i))) 0 0 := by
  have hi : ∀ i : ι, HasDerivAt (fun t : ℂ =>
      ((v i + t * rightCovarianceField S v i) -
        explicitRightInverse (S + t, v i + t * rightCovarianceField S v i)))
      (rightCovarianceField S v i -
        (deriv (fun z => explicitRightInverse (z, v i)) S +
          deriv (fun z => explicitRightInverse (S, z)) (v i) * rightCovarianceField S v i)) 0 := by
    intro i
    have hd : HasDerivAt (fun t : ℂ => v i + t * rightCovarianceField S v i)
        (rightCovarianceField S v i) 0 := by
      simpa only [one_mul, id_eq] using!
        (((hasDerivAt_id (0 : ℂ)).mul_const (rightCovarianceField S v i)).const_add (v i))
    exact hd.sub (analytic_joint_affine_path_hasDerivAt _ S (v i)
      (rightCovarianceField S v i) (hU i))
  have h := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hi i)
  have he : (∑ i, (rightCovarianceField S v i -
        (deriv (fun z => explicitRightInverse (z, v i)) S +
          deriv (fun z => explicitRightInverse (S, z)) (v i) * rightCovarianceField S v i))) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, rightCovarianceField_sum, htransport]
    simp only [rightCovarianceAmplitude, add_neg_cancel, sub_zero]
  exact h.congr_deriv he

/-- Every real nonconstant right-arc tuple has a genuine nonzero complete
variance, even when any proper subset of the coordinates coincides. -/
theorem rightArc_pairVariance_ne_zero (S₀ : ℝ) (hS₀ : 0 < S₀ ∧ S₀ < 2)
    (w : ι → ℝ) (hw : ∀ i, w i ∈ Icc (-rightBranchEndpoint S₀) 0)
    (i j : ι) (hij : w i ≠ w j) :
    pairVariance (fun k => explicitRightInverse
      ((S₀ : ℂ), (rightArcCoordinate S₀ (w k) : ℂ))) ≠ 0 := by
  have heq : (fun k => explicitRightInverse
      ((S₀ : ℂ), (rightArcCoordinate S₀ (w k) : ℂ))) =
      contourCoordinate w (fun _ => 0) := by
    funext k
    rw [explicitRightInverse_on_right_arc S₀ (w k) hS₀ (hw k)]
    simp [contourCoordinate]
  rw [heq]
  exact contour_variance_ne_zero w (fun _ => 0) 0 (by norm_num)
    (fun _ _ => by simp) i j hij

/-- The covariance field produces a genuinely tangent angular velocity
through the full population-dependent Jacobian.  This is the algebraic
tangency in `eq:iso-angular-field` (7.25), not the current identity. -/
theorem rightCovarianceField_angular_tangent (S : ℂ) (v : ι → ℂ)
    (htransport : (∑ i, deriv (fun z => explicitRightInverse (S, z)) (v i) *
      rightCovarianceField S v i) = rightCovarianceAmplitude S v)
    (scale : ℝ) (p m dp dm : ι → ℝ) (V : ι → ℂ)
    (hV : balancedAngularJacobian scale p m dp dm V = fun i =>
      -(deriv (fun z => explicitRightInverse (z, v i)) S +
        deriv (fun z => explicitRightInverse (S, z)) (v i) * rightCovarianceField S v i)) :
    ∑ i, V i = 0 := by
  rw [balancedAngularJacobian_inverse_preserves_sum scale p m dp dm V _ hV]
  rw [Finset.sum_neg_distrib, Finset.sum_add_distrib, htransport]
  simp only [rightCovarianceAmplitude, add_neg_cancel, neg_zero]

/-- The complete balanced Jacobian supplies an actual angular velocity,
with tangency and its dimension-independent inverse bound. -/
theorem exists_rightCovariance_angular_velocity (S : ℂ) (v : ι → ℂ)
    (htransport : (∑ i, deriv (fun z => explicitRightInverse (S, z)) (v i) *
      rightCovarianceField S v i) = rightCovarianceAmplitude S v)
    (p m dp dm : ι → ℝ) (τ L : ℝ)
    (hn : 0 < Fintype.card ι) (hτ : 0 ≤ τ) (hL : 0 ≤ L)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (hm : ∀ i, 0 ≤ m i ∧ m i ≤ 1)
    (hdp : ∀ i, |dp i| ≤ L) (hdm : ∀ i, |dm i| ≤ L)
    (hsmall : 4 * τ * L < 1) :
    ∃ V : ι → ℂ,
      balancedAngularJacobian (τ / Fintype.card ι) p m dp dm V =
        (fun i => -(deriv (fun z => explicitRightInverse (z, v i)) S +
          deriv (fun z => explicitRightInverse (S, z)) (v i) * rightCovarianceField S v i)) ∧
      (∑ i, V i) = 0 ∧
      ‖V‖ ≤ ‖fun i => -(deriv (fun z => explicitRightInverse (z, v i)) S +
          deriv (fun z => explicitRightInverse (S, z)) (v i) * rightCovarianceField S v i)‖ /
        (1 - 4 * τ * L) := by
  obtain ⟨V, hV⟩ := (balancedAngularJacobian_bijective p m dp dm τ L
    hn hτ hL hp hm hdp hdm hsmall).2 (fun i =>
      -(deriv (fun z => explicitRightInverse (z, v i)) S +
        deriv (fun z => explicitRightInverse (S, z)) (v i) * rightCovarianceField S v i))
  exact ⟨V, hV, rightCovarianceField_angular_tangent S v htransport
      (τ / Fintype.card ι) p m dp dm V hV,
    balancedAngularJacobian_inverse_bound p m dp dm V _ τ L
      hn hτ hL hp hm hdp hdm hsmall hV⟩

/-- One actual complex right neighborhood, selected before N, supports
every filled second secant and both exact covariance transport identities.
The general complex variance nonvanishing condition is retained explicitly. -/
theorem exists_rightCovariance_common_domain (S₀ : ℝ) (hS₀ : 0 < S₀ ∧ S₀ < 2) :
    ∃ r c : ℝ, 0 < r ∧ 0 < c ∧
      rightParameterSegment S₀ ⊆ thickening r (rightParameterSegment S₀) ∧
      (∀ S : ℂ, AnalyticOnNhd ℂ (fun z => explicitRightInverse (S, z))
        (rightInverseSliceDomain S₀ r S)) ∧
      (∀ S : ℂ, ∀ a ∈ rightInverseSliceDomain S₀ r S,
        ∀ b ∈ rightInverseSliceDomain S₀ r S,
          c ≤ (dslope (deriv (fun z => explicitRightInverse (S, z))) a b).re) ∧
      ∀ (N : ℕ) (S : ℂ) (v : Fin N → ℂ),
        (∀ i, v i ∈ rightInverseSliceDomain S₀ r S) →
        pairVariance (fun i => explicitRightInverse (S, v i)) ≠ 0 →
        (∑ i, rightCovarianceField S v i) = 0 ∧
        (∑ i, deriv (fun z => explicitRightInverse (S, z)) (v i) *
          rightCovarianceField S v i) = rightCovarianceAmplitude S v ∧
        HasDerivAt (fun t : ℂ => ∑ i,
          ((v i + t * rightCovarianceField S v i) -
            explicitRightInverse (S + t, v i + t * rightCovarianceField S v i))) 0 0 := by
  obtain ⟨r, c, hr, hc, _, hsub, hU, hall, _⟩ :=
    exists_right_inverse_common_convex_neighborhood S₀ hS₀
  have hmem : ∀ S z, z ∈ rightInverseSliceDomain S₀ r S →
      (S, z) ∈ cthickening r (rightParameterSegment S₀) :=
    fun _ _ hz => thickening_subset_cthickening r _ hz
  have hslice : ∀ S : ℂ, AnalyticOnNhd ℂ (fun z => explicitRightInverse (S, z))
      (rightInverseSliceDomain S₀ r S) := by
    intro S z hz
    exact (hU _ (hmem S z hz)).comp
      (f := fun z : ℂ => (S, z)) (analyticAt_const.prod analyticAt_id)
  have hcurv : ∀ S : ℂ, ∀ z ∈ rightInverseSliceDomain S₀ r S,
      c ≤ (deriv (deriv (fun w => explicitRightInverse (S, w))) z).re := by
    intro S z hz
    have hd := hall (S, z) (hmem S z hz)
    rw [hd.2.2.1.deriv]
    exact hd.2.2.2
  refine ⟨r, c, hr, hc, hsub, hslice, ?_, ?_⟩
  · intro S a ha b hb
    exact second_secant_re_lower_bound _ (rightInverseSliceDomain_convex S₀ r S)
      (hslice S) c (hcurv S) ha hb
  · intro N S v hv hvar
    have hw := analyticCovarianceField_weighted (rightCovarianceAmplitude S v)
      (fun z => explicitRightInverse (S, z)) (rightInverseSliceDomain_convex S₀ r S)
      (hslice S) c hc (hcurv S) v hv hvar
    exact ⟨rightCovarianceField_sum S v, hw,
      rightCovarianceField_phase_derivative S v
        (fun i => hU _ (hmem S (v i) (hv i))) hw⟩

/-- On the genuine limiting real right arc the complete covariance
transport needs no separately supplied variance assumption. Partial
coincidences are allowed; only the full equality locus is excluded. -/
theorem rightCovarianceField_on_real_right_arc (S₀ : ℝ) (hS₀ : 0 < S₀ ∧ S₀ < 2)
    (N : ℕ) (w : Fin N → ℝ) (hw : ∀ i, w i ∈ Icc (-rightBranchEndpoint S₀) 0)
    (i j : Fin N) (hij : w i ≠ w j) :
    let v : Fin N → ℂ := fun k => (rightArcCoordinate S₀ (w k) : ℂ)
    (∑ k, rightCovarianceField (S₀ : ℂ) v k) = 0 ∧
      (∑ k, deriv (fun z => explicitRightInverse ((S₀ : ℂ), z)) (v k) *
        rightCovarianceField (S₀ : ℂ) v k) = rightCovarianceAmplitude (S₀ : ℂ) v ∧
      HasDerivAt (fun t : ℂ => ∑ k,
        ((v k + t * rightCovarianceField (S₀ : ℂ) v k) -
          explicitRightInverse ((S₀ : ℂ) + t,
            v k + t * rightCovarianceField (S₀ : ℂ) v k))) 0 0 := by
  obtain ⟨r, _, _, _, hsub, _, _, hfield⟩ := exists_rightCovariance_common_domain S₀ hS₀
  apply hfield N (S₀ : ℂ) (fun k => (rightArcCoordinate S₀ (w k) : ℂ))
  · intro k
    apply hsub
    refine ⟨by simp, ⟨rightArcCoordinate S₀ (w k), ?_, rfl⟩⟩
    rw [← rightArcCoordinate_image S₀ hS₀]
    exact ⟨w k, hw k, rfl⟩
  · exact rightArc_pairVariance_ne_zero S₀ hS₀ w hw i j hij

end IsingBulk.AnisoF002.Isotropic
