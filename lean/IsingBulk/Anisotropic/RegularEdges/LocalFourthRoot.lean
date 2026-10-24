import IsingBulk.Anisotropic.RegularEdges.LocalParticleRoot
import IsingBulk.Anisotropic.Final.ContinuousRootUniqueness
import Mathlib.Analysis.Complex.Convex

namespace IsingBulk.Anisotropic.RegularEdges
noncomputable section
open Set Filter Metric
open scoped Topology

def upperBall (r : ℝ) : Set ℂ := ball 0 r∩{u | 0<u.im}

theorem upperBall_isOpen (r : ℝ) : IsOpen (upperBall r) :=
  isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_im)

theorem upperBall_isPreconnected (r : ℝ) : IsPreconnected (upperBall r) :=
  ((convex_ball (0:ℂ) r).inter (convex_halfSpace_im_gt 0)).isPreconnected

theorem upperBall_nonempty {r : ℝ} (hr : 0<r) : (upperBall r).Nonempty := by
  refine ⟨Complex.I*(r/2:ℝ),?_,?_⟩
  · simp only [mem_ball,dist_zero_right,norm_mul,Complex.norm_I,one_mul,Complex.norm_real,
      Real.norm_eq_abs,abs_of_pos (half_pos hr)]
    linarith
  · simpa only [Set.mem_ofPred_eq,Complex.mul_im,Complex.I_re,Complex.I_im,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,one_mul,zero_add] using half_pos hr

def localFourthRoot (P : ℂ→ℂ) : ℂ→ℂ := localParticleRoot (localParticleRoot P)

theorem localFourthRoot_pow {P : ℂ→ℂ} (hP : P 0≠0) (u : ℂ) :
    localFourthRoot P u^4=P u := by
  change localParticleRoot (localParticleRoot P) u^4=P u
  calc
    _ = (localParticleRoot (localParticleRoot P) u^2)^2 := by ring
    _ = (localParticleRoot P u)^2 := by rw [localParticleRoot_sq (localParticleRoot_ne_zero hP)]
    _ = P u := localParticleRoot_sq hP u

theorem localFourthRoot_analyticAt {P : ℂ→ℂ} (ha : AnalyticAt ℂ P 0) (hP : P 0≠0) :
    AnalyticAt ℂ (localFourthRoot P) 0 :=
  localParticleRoot_analyticAt (localParticleRoot_analyticAt ha hP) (localParticleRoot_ne_zero hP)

theorem localFourthRoot_ne_zero {P : ℂ→ℂ} (hP : P 0≠0) : localFourthRoot P 0≠0 :=
  localParticleRoot_ne_zero (localParticleRoot_ne_zero hP)

/-- A physical fourth-root branch on an upper half-ball has an actual analytic,
nonzero continuation at its boundary center whenever the radicand does. -/
theorem exists_upper_fourth_branch_extension {P f : ℂ→ℂ} {r : ℝ}
    (hr : 0<r) (hPa : AnalyticAt ℂ P 0) (hP0 : P 0≠0)
    (hf : ContinuousOn f (upperBall r)) (hp : ∀u∈upperBall r,f u^4=P u) :
    ∃δ : ℝ,0<δ ∧ δ≤r ∧ ∃g : ℂ→ℂ,AnalyticOnNhd ℂ g (ball 0 δ) ∧
      g 0≠0 ∧ EqOn g f (upperBall δ) := by
  let g := localFourthRoot P
  have hga : AnalyticAt ℂ g 0 := localFourthRoot_analyticAt hPa hP0
  have hg0 : g 0≠0 := localFourthRoot_ne_zero hP0
  have hev := hga.eventually_analyticAt.and (hga.continuousAt.eventually_ne hg0)
  obtain ⟨ε,hε,hεsub⟩ := Metric.mem_nhds_iff.mp hev
  let δ := min r ε
  have hδ : 0<δ := lt_min hr hε
  have hδr : δ≤r := min_le_left _ _
  have hδε : δ≤ε := min_le_right _ _
  have hg : ∀u∈ball (0:ℂ) δ,AnalyticAt ℂ g u ∧ g u≠0 :=
    fun u hu => hεsub (ball_subset_ball hδε hu)
  have hsub : upperBall δ⊆upperBall r := fun _ hu => ⟨ball_subset_ball hδr hu.1,hu.2⟩
  have hgc : ContinuousOn g (upperBall δ) := fun u hu => (hg u hu.1).1.continuousAt.continuousWithinAt
  have hqc : ContinuousOn (fun u => f u/g u) (upperBall δ) :=
    (hf.mono hsub).div hgc (fun u hu => (hg u hu.1).2)
  have hmap : MapsTo (fun u => f u/g u) (upperBall δ) {v : ℂ | v^4=1} := by
    intro u hu
    change (f u/g u)^4=1
    rw [div_pow,hp u (hsub hu),show g u^4=P u from localFourthRoot_pow hP0 u]
    exact div_self (by rw [←show g u^4=P u from localFourthRoot_pow hP0 u]; exact pow_ne_zero _ (hg u hu.1).2)
  obtain ⟨u₀,hu₀⟩ := upperBall_nonempty hδ
  have hc0 : f u₀/g u₀≠0 := by
    intro h
    have hh := hmap hu₀
    change (f u₀/g u₀)^4=1 at hh
    simp only [h,zero_pow (by decide : 4≠0)] at hh
    exact zero_ne_one hh
  refine ⟨δ,hδ,hδr,(fun u => (f u₀/g u₀)*g u),?_,mul_ne_zero hc0 hg0,?_⟩
  · intro u hu
    exact analyticAt_const.mul (hg u hu).1
  · intro u hu
    have hh := (upperBall_isPreconnected δ).constant_of_mapsTo fourthRootsOfOne_finite.isDiscrete hqc hmap hu hu₀
    exact ((div_eq_iff (hg u hu.1).2).mp hh).symm

end
end IsingBulk.Anisotropic.RegularEdges
