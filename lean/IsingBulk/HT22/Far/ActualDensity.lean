import IsingBulk.HT22.Far.ActualScalar
import IsingBulk.HT22.Far.SignedDensityFactor

/-! Actual signed far physical density, with all original source factors. -/
namespace IsingBulk.HT22.Far
noncomputable section
open IsingBulk.Preferred22 IsingBulk.HT22.Tail IsingBulk.HT22.Geometry Set
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

theorem actual_far_density_bound (b : PreferredBranchData) (M : ℝ) (hM : 0<M) :
    ∃ cap : ℝ, 0<cap ∧ cap<b.alpha ∧ ∀ B : PreferredCoareaBump b, B.delta<cap →
    ∃ ε₀ τ₀ δB : ℝ, 0<ε₀ ∧ 0<τ₀ ∧ 0<δB ∧ δB<B.delta ∧
    ∀ d₀ : ℝ, 0<d₀ → ∀ rcut : ℝ → ℝ,
    ContDiff ℝ ∞ rcut → Function.Periodic rcut (2*Real.pi) →
    ∀ j : ℕ, ∃ A : ℝ, ∃ L : ℕ, 0<A ∧
    ∀ a : ℝ, ∀ N : ℕ, 0<N → ∀ ε τ μ r : ℝ,
    0<ε → ε<ε₀ → 0≤τ → τ<τ₀ → d₀≤r → |μ|+r+ε≤M →
    ∀ θ : Fin N → ℝ,
    (∀ i, -δB≤θ i+b.b ∧ θ i≤B.delta) →
    (∀ i, μ-2*r≤θ i+b.b ∧ θ i+b.b≤μ+2*r) →
    ∀ i k : Fin N, (∀ q, θ i≤θ q ∧ θ q≤θ k) → r≤θ k-θ i →
    ‖(2*Real.pi:ℂ)^(N-1)*transportedDensity (Complex.exp (-Complex.I*(a:ℂ))) τ
      preferredPopulationCutoff B.p B.m rcut j (IsingBulk.Branch.radialParameter b.alpha ε) θ‖≤
      farOrderEnvelope A L N*signedJacobianResolvent a b B ε τ θ := by
  obtain ⟨capF,hcapF,hcapFa,hfar⟩ := actual_far_scalar_bound b M hM
  obtain ⟨capC,hcapC,hcapCa,hchart⟩ := actual_collision_source_chart b
  refine ⟨min capF capC,lt_min hcapF hcapC,(min_le_left _ _).trans_lt hcapFa,?_⟩
  intro B hB
  obtain ⟨eF,tF,dF,heF,htF,hdF,hdFB,hfar⟩ := hfar B (hB.trans_le (min_le_left _ _))
  obtain ⟨c,δ,eC,tC,dC,_hc,heC,htC,hdC,hdCB,hchart⟩ := hchart B (hB.trans_le (min_le_right _ _))
  obtain ⟨CJ,eJ,hCJ,heJ,hJ⟩ := signed_actual_JH_bound b B
  let e := min eF (min eC eJ)
  let t := min 1 (min tF tC)
  let d := min dF dC
  refine ⟨e,t,d,lt_min heF (lt_min heC heJ),lt_min zero_lt_one (lt_min htF htC),
    lt_min hdF hdC,(min_le_left _ _).trans_lt hdFB,?_⟩
  intro d₀ hd₀ rcut hrcut hrper j
  obtain ⟨A,L,hA,hscalar⟩ := hfar d₀ hd₀ rcut hrcut hrper j
  refine ⟨2*(CJ*A),L,by positivity,?_⟩
  intro a N hN ε τ μ r hε hεr hτ hτr hr hTM θ hθ hwindow i k hext hgap
  have heps : ε<eF ∧ ε<eC ∧ ε<eJ := by simpa only [e,lt_min_iff] using hεr
  have htaus : τ<1 ∧ τ<tF ∧ τ<tC := by simpa only [t,lt_min_iff] using hτr
  have hboxF (q : Fin N) : -dF≤θ q+b.b ∧ θ q≤B.delta :=
    ⟨by have hd : d≤dF := min_le_left _ _; linarith [(hθ q).1],(hθ q).2⟩
  have hboxC (q : Fin N) : -dC≤θ q+b.b ∧ θ q+b.b≤b.b+B.delta := by
    have hd : d≤dC := min_le_right _ _
    constructor <;> linarith [(hθ q).1,(hθ q).2]
  obtain ⟨Ω,hΩ,hz,hpoint,hR,_hregular⟩ := hchart N hN ε τ μ r hε heps.2.1 hτ htaus.2.2
    (hd₀.trans_le hr) θ hboxC hwindow i k hext hgap
  have hangle (q : Fin N) : θ q∈Icc (-Real.pi-B.delta) B.delta := by
    have hd : d<B.delta := (min_le_left _ _).trans_lt hdFB
    constructor
    · linarith [(hθ q).1,b.b_lt]
    · exact (hθ q).2
  have hσ : ‖Complex.exp (-Complex.I*(a:ℂ))‖≤1 := by
    rw [Complex.norm_exp]
    simp
  have hs := hscalar N hN ε τ μ r hε heps.1 hτ htaus.2.1 hr hTM θ hboxF hwindow i k hext hgap
  have hj := hJ a N hN ε τ hε heps.2.2 hτ htaus.1.le θ hangle
  have hdens := transportedDensity_bound_of_scalar hN _ hσ τ δ preferredPopulationCutoff B.p B.m rcut
    preferredPopulationCutoff_smooth B.smooth B.m_smooth hrcut Ω hΩ hpoint hR j
    (IsingBulk.Branch.radialParameter b.alpha ε) θ hz _ _ (by
      unfold signedJacobianResolvent; positivity) hs hj
  have hnonneg : 0≤signedJacobianResolvent a b B ε τ θ := by
    unfold signedJacobianResolvent; positivity
  have henv : CJ^N*farOrderEnvelope A L N=farOrderEnvelope (CJ*A) L N := by
    unfold farOrderEnvelope shellOrderEnvelope
    rw [mul_div_assoc,mul_pow]
    ring
  calc
    _ ≤ (2*CJ^N*signedJacobianResolvent a b B ε τ θ)*farOrderEnvelope A L N := hdens
    _ = (2*farOrderEnvelope (CJ*A) L N)*signedJacobianResolvent a b B ε τ θ := by rw [←henv];ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (farOrderEnvelope_absorb_factor (by positivity) (by norm_num) hN L) hnonneg

end
end IsingBulk.HT22.Far
