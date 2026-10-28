import IsingBulk.HT22.Tail.LocalizedActualBoundSeed
import IsingBulk.HT22.Tail.LocalizedScalarBound
import IsingBulk.HT22.Transport.FieldNeighborhood.UniformFrameBudget
import IsingBulk.HT22.Far.ConstantBudget

namespace IsingBulk.HT22.Tail
noncomputable section
open IsingBulk.Preferred22 Set
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

theorem actual_localized_scalar_far_bound (b : PreferredBranchData) :
    ∃ cap : ℝ,0<cap ∧ cap<b.alpha ∧ ∀ B : PreferredCoareaBump b,B.delta<cap →
    ∃ ε₀ τ₀ δB : ℝ,0<ε₀ ∧ 0<τ₀ ∧ 0<δB ∧ δB<B.delta ∧
    ∀ N : ℕ,0<N → ∀ W : (Fin N → ℝ) → ℂ,ContDiff ℝ ∞ W →
    ∀ rcut : ℝ → ℝ,ContDiff ℝ ∞ rcut → Function.Periodic rcut (2*Real.pi) →
    ∀ ρ : ℝ,0<ρ → ∀ j : ℕ,∃ C : ℝ,0<C ∧
    ∀ ε τ : ℝ,0<ε → ε<ε₀ → 0≤τ → τ<τ₀ →
    ∀ θ : Fin N → ℝ,(∀ i,-δB≤θ i+b.b ∧ θ i+b.b≤b.b+B.delta) →
    ρ≤preferredAngularDiameter θ →
    ‖scalarIterate τ B.p B.m (localizedSeed τ preferredPopulationCutoff B.p B.m rcut W) j
      (IsingBulk.Branch.radialParameter b.alpha ε) θ‖≤C := by
  let M := 5*Real.pi+1
  have hM : 0<M := by dsimp [M];positivity
  obtain ⟨cS,hcS,hcSa,hseed⟩ := actual_localized_seed_frame_jets b
  obtain ⟨cF,hcF,_hcFa,hfield⟩ := actual_mixed_field_uniform_frame_budget_uniform_cap b M hM
  obtain ⟨cR,hcR,_hcRa,hchart⟩ := actual_right_source_chart b
  refine ⟨min cS (min cF cR),by positivity,(min_le_left _ _).trans_lt hcSa,?_⟩
  intro B hB
  obtain ⟨eS,tS,dS,heS,htS,hdS,hdSB,hseed⟩ := hseed B (hB.trans_le (by simp))
  obtain ⟨eF,tF,dF,heF,htF,hdF,_hdFB,hfield⟩ := hfield B
  obtain ⟨c,δ,eR,tR,dR,_hc,heR,htR,hdR,_hdRB,hchart⟩ := hchart B (hB.trans_le (by simp))
  have hBfield : B.delta<cF := hB.trans_le (by simp)
  let e := min 1 (min eS (min eF eR))
  let t := min tS (min tF tR)
  let d := min dS (min dF dR)
  have hdB : d<B.delta := (min_le_left _ _).trans_lt hdSB
  refine ⟨e,t,d,by positivity,by positivity,by positivity,hdB,?_⟩
  intro N hN W hW rcut hrcut hrper ρ hρ j
  obtain ⟨AS,hAS,hS⟩ := hseed N hN W hW rcut hrcut hrper j
  obtain ⟨AF,hAF,hF⟩ := hfield (j+1)
  let E := max 1 (Real.sqrt M/ρ)
  let BF := (AF*E^(j+2))*(N:ℝ)^(2*(j+1)+2)
  have hBF : 0<BF := by
    have hn : (0:ℝ)<N := by exact_mod_cast hN
    dsimp [BF,E]
    positivity
  refine ⟨AS*(1+2^j*(2*(N:ℝ)*BF))^j,by positivity,?_⟩
  intro ε τ hε hεr hτ hτr θ hθ hfloor
  have heps : ε<1 ∧ ε<eS ∧ ε<eF ∧ ε<eR := by simpa only [e,lt_min_iff] using hεr
  have htaus : τ<tS ∧ τ<tF ∧ τ<tR := by simpa only [t,lt_min_iff] using hτr
  have hdS' : d≤dS := by simp [d]
  have hdF' : d≤dF := by simp [d]
  have hdR' : d≤dR := by simp [d]
  have hbox (d' : ℝ) (hd' : d≤d') (i : Fin N) : -d'≤θ i+b.b ∧ θ i+b.b≤b.b+B.delta :=
    ⟨by linarith [(hθ i).1],(hθ i).2⟩
  have hdiam : 0<preferredAngularDiameter θ := hρ.trans_le hfloor
  obtain ⟨Ω,hΩ,hz,hpoint,hR,_⟩ := hchart N hN ε τ hε heps.2.2.2 hτ htaus.2.2 θ (hbox dR hdR') hdiam
  have hnon : (Finset.univ : Finset (Fin N)).Nonempty := ⟨⟨0,hN⟩,Finset.mem_univ _⟩
  obtain ⟨i,_,hmin⟩ := Finset.exists_min_image Finset.univ θ hnon
  obtain ⟨k,_,hmax⟩ := Finset.exists_max_image Finset.univ θ hnon
  have hext (a : Fin N) : θ i≤θ a ∧ θ a≤θ k :=
    ⟨hmin a (Finset.mem_univ _),hmax a (Finset.mem_univ _)⟩
  let r := θ k-θ i
  let μ := θ i+b.b
  have hdiamr : preferredAngularDiameter θ≤r := by
    apply Metric.diam_le_of_forall_dist_le (show 0≤r by dsimp [r];linarith [(hext k).1])
    rintro _ ⟨a,rfl⟩ _ ⟨v,rfl⟩
    rw [Real.dist_eq,abs_le]
    constructor <;> dsimp [r] <;> linarith [(hext a).1,(hext a).2,(hext v).1,(hext v).2]
  have hρr : ρ≤r := hfloor.trans hdiamr
  have hr : 0<r := hρ.trans_le hρr
  have hμ : |μ|≤2*Real.pi := by
    apply abs_le.mpr
    dsimp [μ]
    constructor <;> linarith [(hθ i).1,(hθ i).2,B.delta_alpha,b.alpha_lt,b.b_lt,Real.pi_pos]
  have hrpi : r≤2*Real.pi := by
    dsimp [r]
    linarith [(hθ i).1,(hθ k).2,B.delta_alpha,b.alpha_lt,b.b_lt]
  have hTM : |μ|+r+ε≤M := by dsimp [M];linarith [Real.pi_pos]
  have hwindow (a : Fin N) : μ-2*r≤θ a+b.b ∧ θ a+b.b≤μ+2*r := by
    dsimp [μ,r]
    constructor <;> linarith [(hext a).1,(hext a).2,(hext k).1]
  have hboxF (a : Fin N) : -dF≤θ a+b.b ∧ θ a≤min cF B.delta :=
    ⟨(hbox dF hdF' a).1,le_min (by linarith [(hθ a).2]) (by linarith [(hθ a).2])⟩
  let s := IsingBulk.Branch.radialParameter b.alpha ε
  have hAj (xs : List (Option (Fin N))) (hxs : xs.length≤j) :
      ‖frameJet τ B.p B.m (localizedSeed τ preferredPopulationCutoff B.p B.m rcut W) xs s θ‖≤AS :=
    hS ε τ hε heps.2.1 hτ htaus.1 θ (hbox dS hdS') hdiam xs hxs
  have hBj (a : Fin N) (xs : List (Option (Fin N))) (hxs : xs.length≤j+1) :
      ‖frameJet τ B.p B.m (fun t x => residualField t (sourceCoordinate τ B.p B.m t x) a) xs s θ‖≤BF/(1:ℝ)^(1+xs.length) := by
    have hb := hF N hN ε τ μ r hε heps.2.2.1 hτ htaus.2.1 hr hTM θ hboxF hwindow i k hext le_rfl xs hxs a
    have ha := Far.far_field_total_jet_bound hAF.le (by positivity : 0< |μ|+r+ε) hTM hρ hρr
      N (2*(j+1)+2) (j+1) xs.length hxs
    simpa only [one_pow,div_one,Nat.add_assoc] using hb.trans ha
  have hmixed := localizedSeed_mixed τ δ preferredPopulationCutoff B.p B.m rcut
    preferredPopulationCutoff_smooth B.smooth B.m_smooth hrcut W hW Ω hΩ hpoint hR
  have hBmix := (source_generator_factors_mixed τ δ B.p B.m B.smooth B.m_smooth Ω hpoint hR).2.2.2
  have hh := scalarIterate_frame_bound τ δ B.p B.m B.smooth B.m_smooth _ Ω hΩ hpoint hR hBmix hmixed
    s θ hz j AS BF 1 1 hAS.le hBF.le (by norm_num) le_rfl le_rfl hAj hBj j le_rfl [] (by simp)
  simpa only [frameJet,List.length_nil,pow_zero,one_pow,div_one,mul_one,zero_add,one_mul] using hh

end
end IsingBulk.HT22.Tail
