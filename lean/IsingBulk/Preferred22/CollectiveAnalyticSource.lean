import IsingBulk.Preferred22.CollectiveCauchyJets

/-! Recovering actual source analyticity from the proved invertible
anisotropic neighborhood; no new geometric premise is introduced. -/
namespace IsingBulk.Preferred22
noncomputable section
open scoped Topology
set_option backward.isDefEq.respectTransparency false

theorem preferredResidualCollective_analyticAt_of_rescaled {N : ℕ} (hN : 0<N)
    (s : ℂ) (q : Fin N → ℂ) (η d : ℝ) (hη : 0<η) (hd : 0<d)
    (hf : AnalyticAt ℂ (preferredRescaledCollective s q η d) 0) :
    AnalyticAt ℂ (fun z : ℂ × (Fin N → ℂ) => preferredResidualCollective z.1 z.2) (s,q) := by
  let a := η/(N:ℝ)^2
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have ha : 0<a := div_pos hη (sq_pos_of_pos hn)
  have haC : (a:ℂ)≠0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hadC : ((a*d:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr (mul_pos ha hd).ne'
  let L := complexAnisotropicScale (E:=Fin N → ℂ) (a:ℂ) ((a*d:ℝ):ℂ) haC hadC
  let F : ℂ × (Fin N → ℂ) → (Fin N → ℂ) := fun z => preferredResidualCollective z.1 z.2
  have he : a*d=η*d/(N:ℝ)^2 := by dsimp [a]; ring
  have hH : AnalyticAt ℂ (fun z => F ((s,q)+L z)) 0 := by
    change AnalyticAt ℂ (fun z : ℂ × (Fin N → ℂ) =>
      F (s+(a:ℂ)*z.1,q+((a*d:ℝ):ℂ) • z.2)) 0
    rw [he]
    exact hf
  have hlin : AnalyticAt ℂ (fun z : ℂ × (Fin N → ℂ) => L.symm (z-(s,q))) (s,q) :=
    (L.symm.analyticAt _).comp (analyticAt_id.sub analyticAt_const)
  have hh := hH.comp_of_eq hlin (by simp)
  apply hh.congr
  exact Filter.Eventually.of_forall (fun z => by simp only [Function.comp_def,
    ContinuousLinearEquiv.apply_symm_apply,add_sub_cancel]; rfl)

end
end IsingBulk.Preferred22
