import IsingBulk.Tail.MixedCompactSourceSet
import IsingBulk.Tail.LeftSectorZGap
import IsingBulk.Tail.ReciprocalProductJets

/-! Uniform compact-root jets in the two active left-sector variables:
parameter displacement and one compact angular displacement. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set Metric
open scoped Topology BigOperators
attribute [local fun_prop] analyticAt_fst analyticAt_snd

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem analytic_iteratedFDeriv_comp_clm (L : E →L[ℂ] F) (f : F → ℂ) (x : E)
    (hf : AnalyticAt ℂ f (L x)) (k : ℕ) :
    iteratedFDeriv ℂ k (f ∘ L) x=(iteratedFDeriv ℂ k f (L x)).compContinuousLinearMap (fun _ => L) := by
  let U := {z | AnalyticAt ℂ f z}
  have hU : IsOpen U := isOpen_analyticAt ℂ f
  have hpre : IsOpen (L ⁻¹' U) := hU.preimage L.continuous
  have hc : ContDiffOn ℂ ⊤ f U := fun z hz => hz.contDiffAt.contDiffWithinAt
  have hh := L.iteratedFDerivWithin_comp_right hc hU.uniqueDiffOn hpre.uniqueDiffOn hf (i := k) (by simp)
  rw [iteratedFDerivWithin_of_isOpen k hpre hf,iteratedFDerivWithin_of_isOpen k hU hf] at hh
  exact hh

theorem analytic_affine_pullback_jet_norm (L : E →L[ℂ] F) (f : F → ℂ) (a : F) (x : E)
    (hf : AnalyticAt ℂ f (L x+a)) (hL : ‖L‖≤1) (k : ℕ) :
    ‖iteratedFDeriv ℂ k (fun z => f (L z+a)) x‖≤‖iteratedFDeriv ℂ k f (L x+a)‖ := by
  let g := fun z : F => f (z+a)
  have hg : AnalyticAt ℂ g (L x) := hf.comp (f := fun z : F => z+a) (analyticAt_id.add analyticAt_const)
  change ‖iteratedFDeriv ℂ k (g ∘ L) x‖≤_
  rw [analytic_iteratedFDeriv_comp_clm L g x hg k]
  have hh := (iteratedFDeriv ℂ k g (L x)).norm_compContinuousLinearMap_le (fun _ => L)
  have hprod : (∏ _i : Fin k,‖L‖)≤1 := Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => hL)
  have hb := hh.trans (mul_le_of_le_one_right (norm_nonneg _) hprod)
  simpa only [g,iteratedFDeriv_comp_add_right] using hb

abbrev ActiveRootData := (ℂ × ℂ) × (ℂ × ℂ)

def activeCompactRoot (p : ActiveRootData) : ℂ :=
  selectedContinuedRoot (p.1.1+p.2.1) (p.1.2*Complex.exp (Complex.I*p.2.2))

theorem activeCompactRoot_analyticAt {s y : ℂ} (hp : (s,y)∈mixedRootPairDomain) :
    AnalyticAt ℂ activeCompactRoot ((s,y),0) := by
  have hh := selectedContinuedRoot_joint_analyticAt hp.1 hp.2.1 hp.2.2
  have hmap : AnalyticAt ℂ (fun p : ActiveRootData =>
      (p.1.1+p.2.1,p.1.2*Complex.exp (Complex.I*p.2.2))) ((s,y),0) := by
    fun_prop
  have hh' : AnalyticAt ℂ (fun p : ℂ × ℂ => selectedContinuedRoot p.1 p.2)
      (s+0,y*Complex.exp (Complex.I*0)) := by simpa using hh
  exact hh'.comp (f := fun p : ActiveRootData => (p.1.1+p.2.1,p.1.2*Complex.exp (Complex.I*p.2.2))) hmap

def activeRootEmbedding (rotate : Bool) : (ℂ × ℂ) →L[ℂ] ActiveRootData :=
  (0 : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)).prod
    ((ContinuousLinearMap.fst ℂ ℂ ℂ).prod (if rotate then ContinuousLinearMap.snd ℂ ℂ ℂ else 0))

theorem activeRootEmbedding_norm (rotate : Bool) : ‖activeRootEmbedding rotate‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  cases rotate <;> simp [activeRootEmbedding,Prod.norm_def,norm_nonneg]

def rotatingCompactRoot (s y : ℂ) (rotate : Bool) (u : ℂ × ℂ) : ℂ :=
  activeCompactRoot (activeRootEmbedding rotate u+((s,y),0))

theorem rotatingCompactRoot_formula (s y : ℂ) (rotate : Bool) (u : ℂ × ℂ) :
    rotatingCompactRoot s y rotate u=selectedContinuedRoot (s+u.1)
      (y*Complex.exp (Complex.I*(if rotate then u.2 else 0))) := by
  cases rotate <;> simp [rotatingCompactRoot,activeRootEmbedding,activeCompactRoot,add_comm]

@[simp] theorem rotatingCompactRoot_zero (s y : ℂ) (rotate : Bool) :
    rotatingCompactRoot s y rotate 0=selectedContinuedRoot s y := by
  rw [rotatingCompactRoot_formula]
  cases rotate <;> simp

theorem rotatingCompactRoot_analyticAt {s y : ℂ} (hp : (s,y)∈mixedRootPairDomain) (rotate : Bool) :
    AnalyticAt ℂ (rotatingCompactRoot s y rotate) 0 := by
  have hh : AnalyticAt ℂ activeCompactRoot (activeRootEmbedding rotate 0+((s,y),0)) := by
    simpa using activeCompactRoot_analyticAt hp
  exact hh.comp (f := fun u => activeRootEmbedding rotate u+((s,y),0))
    (((activeRootEmbedding rotate).analyticAt 0).add analyticAt_const)

theorem compact_rotating_root_uniform_jets (K : Set (ℂ × ℂ)) (hK : IsCompact K)
    (hKD : K⊆mixedRootPairDomain) (J : ℕ) :
    ∃ C : ℝ,0<C ∧ ∀ p∈K,∀ rotate : Bool,∀ k≤J,
      ‖iteratedFDeriv ℂ k (rotatingCompactRoot p.1 p.2 rotate) 0‖≤C := by
  let K' : Set ActiveRootData := (fun p : ℂ × ℂ => (p,(0:ℂ × ℂ))) '' K
  have hK' : IsCompact K' := hK.image (by fun_prop)
  have hA : ∀ p∈K',AnalyticAt ℂ activeCompactRoot p := by
    rintro p ⟨z,hz,rfl⟩
    exact activeCompactRoot_analyticAt (hKD hz)
  obtain ⟨C,hC,hb⟩ := compact_finite_analytic_jets K' hK' activeCompactRoot hA J
  refine ⟨C,hC,?_⟩
  intro p hp rotate k hk
  have hAp : AnalyticAt ℂ activeCompactRoot (activeRootEmbedding rotate 0+(p,0)) := by
    simpa using activeCompactRoot_analyticAt (hKD hp)
  exact (analytic_affine_pullback_jet_norm (activeRootEmbedding rotate) activeCompactRoot (p,0) 0 hAp
    (activeRootEmbedding_norm rotate) k).trans (by simpa using hb (p,0) ⟨p,hp,rfl⟩ k hk)

end
end IsingBulk.Tail
