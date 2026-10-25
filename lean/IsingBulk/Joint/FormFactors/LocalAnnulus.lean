import IsingBulk.Joint.FormFactors.ContourAnnulus

namespace IsingBulk.Joint.FormFactors
noncomputable section
open IsingBulk.Anisotropic.FormFactors Set Filter Metric
open scoped Topology

theorem dispersion_continuousAt {z : Coupling} {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0) :
    ContinuousAt (fun p : Coupling × (ℂ × ℂ) => dispersion p.1 p.2.1 p.2.2) (z,(x,y)) := by
  have hz : ContinuousAt (fun p : Coupling × (ℂ × ℂ) => p.1.1) (z,(x,y)) := continuousAt_fst.comp continuousAt_fst
  have hw : ContinuousAt (fun p : Coupling × (ℂ × ℂ) => p.1.2) (z,(x,y)) := continuousAt_snd.comp continuousAt_fst
  have hxx : ContinuousAt (fun p : Coupling × (ℂ × ℂ) => p.2.1) (z,(x,y)) :=
    continuousAt_fst.comp continuousAt_snd
  have hyy : ContinuousAt (fun p : Coupling × (ℂ × ℂ) => p.2.2) (z,(x,y)) :=
    continuousAt_snd.comp continuousAt_snd
  unfold dispersion dispersionPolynomial A S T
  have hc := Complex.continuous_cosh.continuousAt.comp hz
  have hcl := Complex.continuous_cosh.continuousAt.comp hw
  have hs := Complex.continuous_sinh.continuousAt.comp hz
  have hsl := Complex.continuous_sinh.continuousAt.comp hw
  exact ((hc.mul hcl).sub ((hs.div_const 2).mul (hxx.add (hxx.inv₀ hx)))).sub
    ((hsl.div_const 2).mul (hyy.add (hyy.inv₀ hy)))

/-- A proved admissible radius remains admissible in a complex neighborhood.
No continuity or regularity of the chosen radius function is needed. -/
theorem contourAnnulus_eventually {r : ℝ} {z : Coupling} (h : ContourAnnulus z r) :
    ∀ᶠ w in 𝓝 z, ContourAnnulus w r := by
  let K : Set ℂ := closedBall 0 1 \ ball 0 r
  have hK : IsCompact K := (isCompact_closedBall (0:ℂ) 1).diff isOpen_ball
  have hm (x : ℂ) : x ∈ K ↔ r ≤ ‖x‖ ∧ ‖x‖ ≤ 1 := by
    simp only [K,Set.mem_sdiff,mem_closedBall,mem_ball,dist_zero_right,not_lt]
    exact and_comm
  have he : ∀ᶠ w in 𝓝 z, ∀ p ∈ K ×ˢ K, dispersion w p.1 p.2 ≠ 0 := by
    apply (hK.prod hK).eventually_forall_of_forall_eventually
    intro p hp
    have hx := (hm p.1).mp hp.1
    have hy := (hm p.2).mp hp.2
    exact (dispersion_continuousAt
      (norm_pos_iff.mp (h.1.trans_le hx.1))
      (norm_pos_iff.mp (h.1.trans_le hy.1))).eventually_ne (h.2.2 _ _ hx.1 hx.2 hy.1 hy.2)
  filter_upwards [he] with w hw
  refine ⟨h.1,h.2.1,?_⟩
  intro x y hx hx1 hy hy1
  exact hw (x,y) ⟨(hm x).mpr ⟨hx,hx1⟩,(hm y).mpr ⟨hy,hy1⟩⟩
end
end IsingBulk.Joint.FormFactors
