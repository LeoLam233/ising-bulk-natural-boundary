import IsingBulk.HT22.Kernel.FixedExtension

/-! Fixed-v joint jets on a compact translated source domain. Parameter
variation of the moving branch is included by composition, not discarded. -/
namespace IsingBulk.HT22.Kernel
noncomputable section
open IsingBulk.Preferred22 Set Metric
open scoped Topology
set_option backward.isDefEq.respectTransparency false

def pairShiftImage (t₀ : ℂ) (ρ : ℝ) (D : Set ℂ) : Set (ℂ × ℂ × ℂ) :=
  (fun z : ℂ × ℂ × ℂ =>
    (z.1,z.2.1+preferredMovingBranch z.1,z.2.2+preferredMovingBranch z.1)) ''
    (closedBall t₀ ρ ×ˢ (D ×ˢ D))

theorem pairShiftImage_compact (t₀ : ℂ) (ρ : ℝ) (D : Set ℂ)
    (hD : IsCompact D)
    (hB : ∀ t∈closedBall t₀ ρ, AnalyticAt ℂ preferredMovingBranch t) :
    IsCompact (pairShiftImage t₀ ρ D) := by
  apply ((isCompact_closedBall t₀ ρ).prod (hD.prod hD)).image_of_continuousOn
  intro z hz
  have hb : ContinuousAt (fun z : ℂ × ℂ × ℂ => preferredMovingBranch z.1) z :=
    ContinuousAt.comp (f := fun z : ℂ × ℂ × ℂ => z.1)
      (g := preferredMovingBranch) (hB z.1 hz.1).continuousAt continuousAt_fst
  exact (continuousAt_fst.prodMk (((continuousAt_fst.comp continuousAt_snd).add hb).prodMk
    ((continuousAt_snd.comp continuousAt_snd).add hb))).continuousWithinAt

theorem ordinaryExtension_fixed_domain_jets (d : PreferredBranchData) (ρ c : ℝ)
    (D : Set ℂ) (hρ : 0<ρ) (hD : IsCompact D) (hzero : (0:ℂ)∈D)
    (hgood : ∀ s q r : ℂ, ‖s-preferredSelectedPoint d‖<ρ → q∈D → r∈D →
      PreferredRightRegularPoint c s q r) :
    ∀ j : ℕ, ∃ C : ℝ, 0<C ∧ ∀ s q r : ℂ,
      ‖s-preferredSelectedPoint d‖≤ρ/2 → q∈D → r∈D →
      AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ => ordinaryExtension z.1 z.2.1 z.2.2)
        (s,q+preferredMovingBranch s,r+preferredMovingBranch s) ∧
      ‖iteratedFDeriv ℂ j (fun z : ℂ × ℂ × ℂ => ordinaryExtension z.1 z.2.1 z.2.2)
        (s,q+preferredMovingBranch s,r+preferredMovingBranch s)‖≤C := by
  let K := pairShiftImage (preferredSelectedPoint d) (ρ/2) D
  have hB : ∀ s∈closedBall (preferredSelectedPoint d) (ρ/2),
      AnalyticAt ℂ preferredMovingBranch s := by
    intro s hs
    have hdist : ‖s-preferredSelectedPoint d‖≤ρ/2 := by
      simpa only [mem_closedBall,dist_eq_norm] using hs
    exact (hgood s 0 0 (by linarith) hzero hzero).1
  have hK : IsCompact K := pairShiftImage_compact _ _ _ hD hB
  have ha : AnalyticOnNhd ℂ
      (fun z : ℂ × ℂ × ℂ => ordinaryExtension z.1 z.2.1 z.2.2) K := by
    rintro z ⟨⟨s,q,r⟩,⟨hs,hq,hr⟩,rfl⟩
    have hdist : ‖s-preferredSelectedPoint d‖≤ρ/2 := by
      simpa only [mem_closedBall,dist_eq_norm] using hs
    apply ordinaryExtension_analyticAt c
    simpa only [add_sub_cancel_right] using hgood s q r (by linarith) hq hr
  intro j
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn (fun z hz =>
    ((ha.iteratedFDeriv j) z hz).continuousAt.continuousWithinAt)
  refine ⟨max C 0+1,by positivity,?_⟩
  intro s q r hs hq hr
  have hm : (s,q+preferredMovingBranch s,r+preferredMovingBranch s)∈K :=
    ⟨(s,q,r),⟨by simpa only [mem_closedBall,dist_eq_norm] using hs,hq,hr⟩,rfl⟩
  exact ⟨ha _ hm,(hC _ hm).trans (by have := le_max_left C 0;linarith)⟩

end
end IsingBulk.HT22.Kernel
