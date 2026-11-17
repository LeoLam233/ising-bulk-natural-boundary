import IsingBulk.AnisoF002.C03.IsotropicHomotopyDifferential

/-!
# Differentiation on the original affine constraint chart

The last real angle is eliminated by its exact sum constraint. Its
Jacobian sends an independent coordinate direction to e_i - e_last.
Consequently a tangent full current restricts to the ordinary real
Lebesgue divergence of the first N-1 components.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators
open Set Filter

def constrainedTangentMap (n : ℕ) : (Fin n → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) :=
  ContinuousLinearMap.pi (fun j => Fin.lastCases
    (-(∑ i : Fin n, ContinuousLinearMap.proj i))
    (fun i => ContinuousLinearMap.proj i) j)

theorem constrainedTangentMap_apply {n : ℕ} (x : Fin n → ℝ) :
    constrainedTangentMap n x = Fin.snoc x (-∑ i, x i) := by
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp [constrainedTangentMap]
  · simp [constrainedTangentMap]

def affineConstraintAngles {n : ℕ} (a : ℝ) (x : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  constrainedTangentMap n x + Pi.single (Fin.last n) a

theorem affineConstraintAngles_eq_snoc {n : ℕ} (a : ℝ) (x : Fin n → ℝ) :
    affineConstraintAngles a x = Fin.snoc x (a - ∑ i, x i) := by
  rw [affineConstraintAngles, constrainedTangentMap_apply]
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp
    ring
  · simp

theorem affineConstraintAngles_contDiff {n : ℕ} (a : ℝ) (k : ℕ∞) :
    ContDiff ℝ k (affineConstraintAngles (n := n) a) :=
  (constrainedTangentMap n).contDiff.add contDiff_const

theorem constrainedTangentMap_single {n : ℕ} (i : Fin n) :
    constrainedTangentMap n (Pi.single i 1) =
      Pi.single i.castSucc 1 - Pi.single (Fin.last n) 1 := by
  rw [constrainedTangentMap_apply]
  funext j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simp
  · simp [Pi.single_apply, Fin.castSucc_inj]

theorem affineConstraintAngles_hasFDerivAt {n : ℕ} (a : ℝ) (x : Fin n → ℝ) :
    HasFDerivAt (affineConstraintAngles a) (constrainedTangentMap n) x := by
  exact (constrainedTangentMap n).hasFDerivAt.add_const _

theorem scalarPartial_affineConstraint_comp {n : ℕ} (a : ℝ)
    (f : (Fin (n + 1) → ℝ) → ℂ) (x : Fin n → ℝ) (i : Fin n)
    (hf : DifferentiableAt ℝ f (affineConstraintAngles a x)) :
    scalarPartial (fun y => f (affineConstraintAngles a y)) (Pi.single i 1) x =
      scalarPartial f (Pi.single i.castSucc 1 - Pi.single (Fin.last n) 1)
        (affineConstraintAngles a x) := by
  have hd := hf.hasFDerivAt.comp x (affineConstraintAngles_hasFDerivAt a x)
  simp only [Function.comp_def] at hd
  rw [scalarPartial, hd.fderiv, ContinuousLinearMap.comp_apply, constrainedTangentMap_single]
  rfl

/-- The exact divergence in the actual eliminated-angle chart. -/
theorem affineConstraint_tangent_divergence {n : ℕ} (a : ℝ)
    (F : Fin (n + 1) → (Fin (n + 1) → ℝ) → ℂ) (x : Fin n → ℝ)
    (hF : ∀ i, DifferentiableAt ℝ (F i) (affineConstraintAngles a x))
    (htangent : (fun y => ∑ i, F i y) =ᶠ[𝓝 (affineConstraintAngles a x)] (fun _ => 0)) :
    (∑ i, scalarPartial (fun y => F i.castSucc (affineConstraintAngles a y))
      (Pi.single i 1) x) =
      ∑ i, scalarPartial (F i) (Pi.single i 1) (affineConstraintAngles a x) := by
  simp_rw [scalarPartial_affineConstraint_comp a _ x _ (hF _)]
  have hz : ∑ i, scalarPartial (F i) (Pi.single (Fin.last n) 1)
      (affineConstraintAngles a x) = 0 := by
    rw [← scalarPartial_sum F _ _ hF]
    unfold scalarPartial
    rw [htangent.fderiv_eq, fderiv_const_apply]
    rfl
  rw [Fin.sum_univ_castSucc] at hz ⊢
  simp only [scalarPartial, map_sub, Finset.sum_sub_distrib]
  change (∑ i : Fin n, scalarPartial (F i.castSucc) (Pi.single i.castSucc 1)
      (affineConstraintAngles a x)) -
      (∑ i : Fin n, scalarPartial (F i.castSucc) (Pi.single (Fin.last n) 1)
        (affineConstraintAngles a x)) = _
  simp only [scalarPartial] at hz ⊢
  linear_combination -hz

end IsingBulk.AnisoF002.Isotropic
