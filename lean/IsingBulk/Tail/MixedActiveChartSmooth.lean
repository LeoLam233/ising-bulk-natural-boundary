import IsingBulk.Tail.MixedActiveDivergence

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Jets Set Filter
open scoped Topology BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false

theorem mixedFreeze_contDiff {N : ℕ} (S : Finset (Fin N)) (background : Fin N → ℝ) :
    ContDiff ℝ ∞ (mixedFreeze S background) := by
  apply contDiff_pi.mpr
  intro i
  by_cases hi : i∈S
  · simpa only [mixedFreeze,hi,ite_true] using contDiff_apply ℝ ℝ i
  · simp only [mixedFreeze,hi,ite_false]
    exact contDiff_const

theorem mixedSourceDisplacement_contDiffAt {N : ℕ} (J : Finset (Fin N)) (j q : Fin N)
    (f : SelectorFunctions) {r : ℝ} (hr : 0<r) (τ lam : ℝ)
    (s : ℂ) (background : Fin N → ℝ) (t : ℂ) (x : Fin N → ℝ)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m)
    (hΩ : (t,mixedFreeze (insert q J) background x)∈mixedSeparatedDomain J j q f r τ lam) :
    ContDiffAt ℝ ∞ (fun p : ℂ × (Fin N → ℝ) =>
      mixedSourceDisplacement J q f r τ lam s background p.1 p.2) (t,x) := by
  let H := fun p : ℂ × (Fin N → ℝ) => (p.1,mixedFreeze (insert q J) background p.2)
  have hH : ContDiff ℝ ∞ H := contDiff_fst.prodMk ((mixedFreeze_contDiff _ _).comp contDiff_snd)
  have hφ (i : Fin N) : ContDiffAt ℝ ∞ (fun p : ℂ × (Fin N → ℝ) =>
      mixedContourPhase f r τ lam p.1 (mixedFreeze (insert q J) background p.2) i) (t,x) := by
    have hh := ((mixedSeparated_phase_smooth J j q f hr τ lam hp hm i) _ hΩ).1.comp
      (t,x) hH.contDiffAt
    exact hh
  have hbranch : ContDiffAt ℝ ∞ (fun p : ℂ × (Fin N → ℝ) => fun i => if i∈J then
      mixedContourPhase f r τ lam p.1 (mixedFreeze (insert q J) background p.2) i-
        mixedContourPhase f r τ lam s background i else 0) (t,x) := by
    apply contDiffAt_pi.mpr
    intro i
    by_cases hi : i∈J
    · simpa only [hi,ite_true] using (hφ i).sub contDiffAt_const
    · simp only [hi,ite_false]
      exact contDiffAt_const
  have hq : ContDiff ℝ ∞ (fun p : ℂ × (Fin N → ℝ) =>
      (mixedFreeze (insert q J) background p.2 q:ℂ)-(background q:ℂ)) := by
    simp only [mixedFreeze,Finset.mem_insert_self,ite_true]
    have ho : ContDiff ℝ ∞ Complex.ofReal := Complex.ofRealCLM.contDiff
    fun_prop
  exact (contDiffAt_fst.sub contDiffAt_const).prodMk (hbranch.prodMk hq.contDiffAt)

end
end IsingBulk.Tail
