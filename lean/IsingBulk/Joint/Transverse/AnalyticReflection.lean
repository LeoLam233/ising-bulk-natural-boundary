import IsingBulk.Joint.Transverse.SymmetryTransport
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-! Reflection of convergent multivariable complex power series. The
coefficients below are complex multilinear because both the source slots
and the target are conjugated. Their operator norms do not increase. -/
namespace IsingBulk.Joint.Transverse
noncomputable section
open Set Filter Metric
open scoped Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [StarAddMonoid E] [StarModule ℂ E] [NormedStarGroup E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [StarAddMonoid F] [StarModule ℂ F] [NormedStarGroup F]

def reflectedMultilinear {n : ℕ} (p : E [×n]→L[ℂ] F) : E [×n]→L[ℂ] F where
  toFun m := star (p (star m))
  map_update_add' m i x y := by
    rw [←Function.update_star,star_add,p.map_update_add,star_add]
    rw [←Function.update_star,←Function.update_star]
  map_update_smul' m i c x := by
    rw [←Function.update_star,star_smul,p.map_update_smul,star_smul,star_star]
    rw [←Function.update_star]
  cont := continuous_star.comp (p.cont.comp continuous_star)

theorem reflectedMultilinear_norm_le {n : ℕ} (p : E [×n]→L[ℂ] F) :
    ‖reflectedMultilinear p‖≤‖p‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg p)
  intro m
  change ‖star (p (star m))‖≤_
  simpa only [norm_star,Pi.star_apply] using p.le_opNorm (star m)

def reflectedPowerSeries (p : FormalMultilinearSeries ℂ E F) :
    FormalMultilinearSeries ℂ E F := fun n => reflectedMultilinear (p n)

/-- Joint analyticity is preserved by reflection in any complex normed
spaces with isometric conjugations. No finite-dimensional holomorphic-to-
analytic theorem, or additional analytic-family hypothesis, is assumed. -/
theorem analyticAt_star_star {f : E → F} {x : E} (hf : AnalyticAt ℂ f x) :
    AnalyticAt ℂ (fun y => star (f (star y))) (star x) := by
  obtain ⟨p,r,hp⟩ := hf
  refine ⟨reflectedPowerSeries p,r,?_⟩
  refine ⟨hp.r_le.trans (FormalMultilinearSeries.radius_le_of_le
    (fun n => reflectedMultilinear_norm_le (p n))),hp.r_pos,?_⟩
  intro y hy
  have hys : star y∈eball (0:E) r := by
    have he : edist (star y) (0:E)=edist y 0 := by
      simpa only [star_zero] using edist_star_star y (0:E)
    change edist (star y) 0<r
    rw [he]
    exact hy
  have hh := (hp.hasSum hys).star
  convert! hh using 1
  simp only [star_add,star_star]

end
end IsingBulk.Joint.Transverse
