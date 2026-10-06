import IsingBulk.Tail.LeftFrozenCompactJets

namespace IsingBulk.Tail
noncomputable section
open Set
attribute [local fun_prop] analyticAt_fst analyticAt_snd

def activeCompactCoefficient (F : ℂ → ℂ → ℂ) (p : ActiveRootData) : ℂ :=
  F (p.1.1+p.2.1) (p.1.2*Complex.exp (Complex.I*p.2.2))

def rotatingCompactCoefficient (F : ℂ → ℂ → ℂ) (s y : ℂ) (rotate : Bool) (u : ℂ × ℂ) : ℂ :=
  activeCompactCoefficient F (activeRootEmbedding rotate u+((s,y),0))

theorem rotatingCompactCoefficient_formula (F : ℂ → ℂ → ℂ) (s y : ℂ) (rotate : Bool) (u : ℂ × ℂ) :
    rotatingCompactCoefficient F s y rotate u=F (s+u.1)
      (y*Complex.exp (Complex.I*(if rotate then u.2 else 0))) := by
  cases rotate <;> simp [rotatingCompactCoefficient,activeRootEmbedding,activeCompactCoefficient,add_comm]

theorem activeCompactCoefficient_analyticAt (F : ℂ → ℂ → ℂ) {s y : ℂ}
    (hF : AnalyticAt ℂ (fun p : ℂ × ℂ => F p.1 p.2) (s,y)) :
    AnalyticAt ℂ (activeCompactCoefficient F) ((s,y),0) := by
  have hmap : AnalyticAt ℂ (fun p : ActiveRootData =>
      (p.1.1+p.2.1,p.1.2*Complex.exp (Complex.I*p.2.2))) ((s,y),0) := by fun_prop
  have hh : AnalyticAt ℂ (fun p : ℂ × ℂ => F p.1 p.2)
      (s+0,y*Complex.exp (Complex.I*0)) := by simpa using hF
  exact hh.comp (f := fun p : ActiveRootData => (p.1.1+p.2.1,p.1.2*Complex.exp (Complex.I*p.2.2))) hmap

theorem compact_rotating_coefficient_uniform_jets (K : Set (ℂ × ℂ)) (hK : IsCompact K)
    (F : ℂ → ℂ → ℂ) (hF : ∀ p∈K,AnalyticAt ℂ (fun z : ℂ × ℂ => F z.1 z.2) p) (J : ℕ) :
    ∃ C : ℝ,0<C ∧ ∀ p∈K,∀ rotate : Bool,
      AnalyticAt ℂ (rotatingCompactCoefficient F p.1 p.2 rotate) 0 ∧ ∀ k≤J,
      ‖iteratedFDeriv ℂ k (rotatingCompactCoefficient F p.1 p.2 rotate) 0‖≤C := by
  let K' : Set ActiveRootData := (fun p : ℂ × ℂ => (p,(0:ℂ × ℂ))) '' K
  have hK' : IsCompact K' := hK.image (by fun_prop)
  have hA : ∀ p∈K',AnalyticAt ℂ (activeCompactCoefficient F) p := by
    rintro p ⟨z,hz,rfl⟩
    exact activeCompactCoefficient_analyticAt F (hF z hz)
  obtain ⟨C,hC,hb⟩ := compact_finite_analytic_jets K' hK' _ hA J
  refine ⟨C,hC,?_⟩
  intro p hp rotate
  have hAp : AnalyticAt ℂ (activeCompactCoefficient F) (activeRootEmbedding rotate 0+(p,0)) := by
    simpa using activeCompactCoefficient_analyticAt F (hF p hp)
  refine ⟨hAp.comp (f := fun u => activeRootEmbedding rotate u+(p,0))
    (((activeRootEmbedding rotate).analyticAt 0).add analyticAt_const),?_⟩
  intro k hk
  exact (analytic_affine_pullback_jet_norm (activeRootEmbedding rotate) _ (p,0) 0 hAp
    (activeRootEmbedding_norm rotate) k).trans (by simpa using hb (p,0) ⟨p,hp,rfl⟩ k hk)

end
end IsingBulk.Tail
