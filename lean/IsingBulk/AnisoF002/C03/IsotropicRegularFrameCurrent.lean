import IsingBulk.AnisoF002.C03.IsotropicScalarCurrentIdentity

/-!
# The exact current in its regular coordinate frame

The regular frame is built from the actual coordinate derivative. This
rewrites the proved scalar current in the precise coordinate-frame form
used in frozen F002, without an assumed divergence identity.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators Matrix
open Set Filter

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def scalarFrameApplied (M : Matrix ι ι ℂ) (db : ι → ℂ) (i : ι) : ℂ :=
  ∑ l, M⁻¹ l i * db l

def scalarFrameParameter (M : Matrix ι ι ℂ) (χa db : ι → ℂ) (ba : ℂ) : ℂ :=
  ba - (M⁻¹ *ᵥ χa) ⬝ᵥ db

theorem scalar_frame_transport_algebra (M : Matrix ι ι ℂ)
    (χa V B db : ι → ℂ) (ba : ℂ) (hM : M.det ≠ 0)
    (hB : B = χa - M *ᵥ V) :
    ba - (∑ i, V i * db i) =
      scalarFrameParameter M χa db ba + ∑ i, B i * scalarFrameApplied M db i := by
  have hV : M⁻¹ *ᵥ B = M⁻¹ *ᵥ χa - V := by
    rw [hB, Matrix.mulVec_sub, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.mpr hM), Matrix.one_mulVec]
  have he : (∑ i, B i * scalarFrameApplied M db i) = (M⁻¹ *ᵥ B) ⬝ᵥ db := by
    simp only [scalarFrameApplied, Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [he, hV, sub_dotProduct]
  unfold scalarFrameParameter
  change ba - V ⬝ᵥ db = _
  ring

theorem scalar_frame_divergence_algebra (M DB : Matrix ι ι ℂ) :
    scalarRegularDivergence M DB = ∑ i, scalarFrameApplied M (fun l => DB i l) i := by
  simp only [scalarRegularDivergence, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    scalarFrameApplied]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro l _
  exact mul_comm _ _

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def scalarRegularFrameDerivative (χ : ι → E → ℂ) (e : ι → E)
    (b : E → ℂ) (i : ι) (x : E) : ℂ :=
  scalarFrameApplied (scalarCoordinateMatrix χ e x) (fun l => scalarPartial b (e l) x) i

def scalarRegularParameterDerivative (χ : ι → E → ℂ) (e : ι → E)
    (a : E) (b : E → ℂ) (x : E) : ℂ :=
  scalarFrameParameter (scalarCoordinateMatrix χ e x)
    (fun i => scalarPartial (χ i) a x) (fun i => scalarPartial b (e i) x)
    (scalarPartial b a x)

/-- Frozen F002's current formula in the actual coordinate frame. The
amplitude may be any differentiable complex function of the real
variables, including smooth real cutoffs and transported amplitudes. -/
theorem exact_regular_frame_current (χ : ι → E → ℂ) (e : ι → E) (a x : E)
    (V : ι → E → ℂ) (b : E → ℂ)
    (hχ : ∀ i, ContDiffAt ℝ 2 (χ i) x)
    (hV : ∀ i, DifferentiableAt ℝ (V i) x) (hb : DifferentiableAt ℝ b x)
    (hdet : scalarCoordinateDet χ e x ≠ 0) :
    scalarPartial (fun y => scalarCoordinateDet χ e y * b y) a x -
        (∑ i, scalarPartial (fun y => V i y * scalarCoordinateDet χ e y * b y) (e i) x) =
      scalarCoordinateDet χ e x *
        (scalarRegularParameterDerivative χ e a b x +
          (∑ i, scalarTransportVelocity χ e a V x i * scalarRegularFrameDerivative χ e b i x) +
          (∑ i, scalarRegularFrameDerivative χ e
            (fun y => scalarTransportVelocity χ e a V y i) i x) * b x) := by
  rw [exact_scalar_current χ e a x V b hχ hV hb hdet]
  have hB : scalarTransportVelocity χ e a V x =
      (fun i => scalarPartial (χ i) a x) - scalarCoordinateMatrix χ e x *ᵥ (fun i => V i x) := by
    rfl
  have ht := scalar_frame_transport_algebra (scalarCoordinateMatrix χ e x)
    (fun i => scalarPartial (χ i) a x) (fun i => V i x)
    (scalarTransportVelocity χ e a V x) (fun i => scalarPartial b (e i) x)
    (scalarPartial b a x) hdet hB
  rw [ht]
  have hd := scalar_frame_divergence_algebra (scalarCoordinateMatrix χ e x)
    (scalarCoordinateMatrix (fun i y => scalarTransportVelocity χ e a V y i) e x)
  change scalarRegularDivergence _ _ = _ at hd
  rw [show scalarTransportDivergence χ e a V x =
    ∑ i, scalarRegularFrameDerivative χ e (fun y => scalarTransportVelocity χ e a V y i) i x
    from hd]
  rfl

/-- A tangent current has exactly the constrained real divergence. This
identity uses the derivatives along the original real angular vectors;
it does not introduce an intrinsic complex integration measure. -/
theorem tangent_current_constrained_divergence (F : ι → E → ℂ)
    (e : ι → E) (x : E) (a : ι)
    (hF : ∀ i, DifferentiableAt ℝ (F i) x)
    (htangent : (fun y => ∑ i, F i y) =ᶠ[𝓝 x] (fun _ => 0)) :
    (∑ i ∈ Finset.univ.erase a, scalarPartial (F i) (e i - e a) x) =
      ∑ i, scalarPartial (F i) (e i) x := by
  have hz : (∑ i, scalarPartial (F i) (e a) x) = 0 := by
    rw [← scalarPartial_sum F (e a) x hF]
    unfold scalarPartial
    rw [htangent.fderiv_eq, fderiv_const_apply]
    rfl
  have hA := Finset.sum_erase_add Finset.univ
    (fun i => scalarPartial (F i) (e i) x) (Finset.mem_univ a)
  have hB := Finset.sum_erase_add Finset.univ
    (fun i => scalarPartial (F i) (e a) x) (Finset.mem_univ a)
  rw [hz] at hB
  have hs : (∑ i ∈ Finset.univ.erase a, scalarPartial (F i) (e i - e a) x) =
      (∑ i ∈ Finset.univ.erase a, scalarPartial (F i) (e i) x) -
      ∑ i ∈ Finset.univ.erase a, scalarPartial (F i) (e a) x := by
    simp only [scalarPartial, map_sub, Finset.sum_sub_distrib]
  rw [hs]
  linear_combination hA - hB

end IsingBulk.AnisoF002.Isotropic
