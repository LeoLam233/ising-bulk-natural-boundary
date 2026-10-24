import IsingBulk.Anisotropic.RegularEdges.AngularNumeratorBridge
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle

namespace IsingBulk.Anisotropic.RegularEdges
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.HT.Contour Set
open scoped BigOperators

def wrapAngle (q : ℝ) : ℝ := (q:Real.Angle).toReal

theorem wrapAngle_mem (q : ℝ) : wrapAngle q∈Icc (-Real.pi) Real.pi :=
  ⟨(Real.Angle.neg_pi_lt_toReal _).le,Real.Angle.toReal_le_pi _⟩

@[simp] theorem cos_wrapAngle (q : ℝ) : Real.cos (wrapAngle q)=Real.cos q := by
  simp [wrapAngle]
@[simp] theorem sin_wrapAngle (q : ℝ) : Real.sin (wrapAngle q)=Real.sin q := by
  simp [wrapAngle]
@[simp] theorem limitingAngle_wrapAngle (q : ℝ) : limitingAngle (wrapAngle q)=limitingAngle q := by
  simp only [limitingAngle,Complex.exp_mul_I,← Complex.ofReal_cos,← Complex.ofReal_sin,
    cos_wrapAngle,sin_wrapAngle]

@[simp] theorem edgeParamRoot_wrapAngle (b : ℝ) (B : ℂ → ℂ) (u : ℂ) (q : ℝ) :
    edgeParamRoot b B u (wrapAngle q)=edgeParamRoot b B u q := by
  simp only [edgeParamRoot,edgeParamW,cos_wrapAngle]

@[simp] theorem transferRoot_wrapAngle (lam : ℝ) (z : ℂ) (q : ℝ) :
    transferRoot lam z (wrapAngle q:ℂ)=transferRoot lam z (q:ℂ) := by
  simp only [transferRoot,transferW,← Complex.ofReal_cos,cos_wrapAngle]

theorem angularRootPair_wrapAngle (r s : ℂ) (q t : ℝ) :
    angularRootPair r s (wrapAngle q:ℂ) (wrapAngle t:ℂ)=angularRootPair r s (q:ℂ) (t:ℂ) := by
  rw [← canceledPair_unit_eq_angularRootPair,← canceledPair_unit_eq_angularRootPair]
  rw [limitingAngle_wrapAngle,limitingAngle_wrapAngle]

theorem complexAngularDensity_wrapAngle {N : ℕ} (lam : ℝ) (z : ℂ) (q : Fin N → ℝ) :
    complexAngularDensity lam z (fun i => (wrapAngle (q i):ℂ))=
      complexAngularDensity lam z (fun i => (q i:ℂ)) := by
  simp only [complexAngularDensity,complexAngularWeight,transferRoot_wrapAngle,angularRootPair_wrapAngle]

theorem edgeNumerator_map_wrapAngle (b : ℝ) (B S : ℂ → ℂ) (u : ℂ) (qs : List ℝ) :
    edgeNumerator b B S u (qs.map wrapAngle)=edgeNumerator b B S u qs := by
  unfold edgeNumerator radialEdgePairProduct
  have hy : (qs.map wrapAngle).map (radialEdgeY 1)=qs.map (radialEdgeY 1) := by
    simp only [List.map_map]
    apply List.map_congr_left
    intro q _
    simp only [Function.comp_apply,radialEdgeY_one,limitingAngle_wrapAngle]
  have ho : (qs.map wrapAngle).map (edgeOneBody b B S u)=qs.map (edgeOneBody b B S u) := by
    simp only [List.map_map]
    apply List.map_congr_left
    intro q _
    simp only [Function.comp_apply,edgeOneBody,edgeParamRoot_wrapAngle]
  rw [hy,ho]

end
end IsingBulk.Anisotropic.RegularEdges
