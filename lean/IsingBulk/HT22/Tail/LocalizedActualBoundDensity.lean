import IsingBulk.HT22.Tail.LocalizedActualBoundScalar
import IsingBulk.HT22.Far.SignedDensityFactor

namespace IsingBulk.HT22.Tail
noncomputable section
open IsingBulk.Preferred22 IsingBulk.HT22.Geometry Set
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

/-- Actual arbitrary smooth localized physical transport, bounded by the
same original signed coarea density away from full equality. -/
theorem actual_localized_density_far_bound (b : PreferredBranchData) :
    ∃ cap : ℝ,0<cap ∧ cap<b.alpha ∧ ∀ B : PreferredCoareaBump b,B.delta<cap →
    ∃ ε₀ τ₀ δB : ℝ,0<ε₀ ∧ 0<τ₀ ∧ 0<δB ∧ δB<B.delta ∧
    ∀ N : ℕ,0<N → ∀ W : (Fin N → ℝ) → ℂ,ContDiff ℝ ∞ W →
    ∀ rcut : ℝ → ℝ,ContDiff ℝ ∞ rcut → Function.Periodic rcut (2*Real.pi) →
    ∀ ρ : ℝ,0<ρ → ∀ j : ℕ,∃ C : ℝ,0<C ∧ ∀ a : ℝ,
    ∀ ε τ : ℝ,0<ε → ε<ε₀ → 0≤τ → τ<τ₀ →
    ∀ θ : Fin N → ℝ,(∀ i,-δB≤θ i+b.b ∧ θ i+b.b≤b.b+B.delta) →
    ρ≤preferredAngularDiameter θ →
    ‖localizedPhysicalDensity (Complex.exp (-Complex.I*(a:ℂ))) τ preferredPopulationCutoff B.p B.m rcut W j
      (IsingBulk.Branch.radialParameter b.alpha ε) θ‖≤C*signedJacobianResolvent a b B ε τ θ := by
  obtain ⟨cS,hcS,hcSa,hscalar⟩ := actual_localized_scalar_far_bound b
  obtain ⟨cR,hcR,_hcRa,hchart⟩ := actual_right_source_chart b
  refine ⟨min cS cR,lt_min hcS hcR,(min_le_left _ _).trans_lt hcSa,?_⟩
  intro B hB
  obtain ⟨eS,tS,dS,heS,htS,hdS,hdSB,hscalar⟩ := hscalar B (hB.trans_le (min_le_left _ _))
  obtain ⟨c,δ,eR,tR,dR,_hc,heR,htR,hdR,_hdRB,hchart⟩ := hchart B (hB.trans_le (min_le_right _ _))
  obtain ⟨CJ,eJ,hCJ,heJ,hJ⟩ := Far.signed_actual_JH_bound b B
  let e := min eS (min eR eJ)
  let t := min 1 (min tS tR)
  let d := min dS dR
  have hdB : d<B.delta := (min_le_left _ _).trans_lt hdSB
  refine ⟨e,t,d,lt_min heS (lt_min heR heJ),lt_min zero_lt_one (lt_min htS htR),
    lt_min hdS hdR,hdB,?_⟩
  intro N hN W hW rcut hrcut hrper ρ hρ j
  obtain ⟨CS,hCS,hscalar⟩ := hscalar N hN W hW rcut hrcut hrper ρ hρ j
  refine ⟨2*CJ^N*CS,by positivity,?_⟩
  intro a ε τ hε hεr hτ hτr θ hθ hfloor
  have heps : ε<eS ∧ ε<eR ∧ ε<eJ := by simpa only [e,lt_min_iff] using hεr
  have htaus : τ<1 ∧ τ<tS ∧ τ<tR := by simpa only [t,lt_min_iff] using hτr
  have hbox (d' : ℝ) (hd' : d≤d') (i : Fin N) : -d'≤θ i+b.b ∧ θ i+b.b≤b.b+B.delta :=
    ⟨by linarith [(hθ i).1],(hθ i).2⟩
  have hs := hscalar ε τ hε heps.1 hτ htaus.2.1 θ (hbox dS (min_le_left _ _)) hfloor
  obtain ⟨Ω,hΩ,hz,hpoint,hR,_⟩ := hchart N hN ε τ hε heps.2.1 hτ htaus.2.2 θ
    (hbox dR (min_le_right _ _)) (hρ.trans_le hfloor)
  have hσ : ‖Complex.exp (-Complex.I*(a:ℂ))‖≤1 := by rw [Complex.norm_exp];simp
  have hangle (i : Fin N) : θ i∈Icc (-Real.pi-B.delta) B.delta := by
    constructor <;> linarith [(hθ i).1,(hθ i).2,b.b_lt]
  have hj := hJ a N hN ε τ hε heps.2.2 hτ htaus.1.le θ hangle
  rw [localizedPhysicalDensity_factorization hN _ hσ τ δ preferredPopulationCutoff B.p B.m rcut
    preferredPopulationCutoff_smooth B.smooth B.m_smooth hrcut W hW Ω hΩ hpoint hR j _ θ hz,norm_mul]
  have hnonneg : 0≤signedJacobianResolvent a b B ε τ θ := by unfold signedJacobianResolvent;positivity
  have hh := mul_le_mul hj hs (norm_nonneg _) (by positivity : 0≤2*CJ^N*signedJacobianResolvent a b B ε τ θ)
  convert hh using 1; ring

end
end IsingBulk.HT22.Tail
