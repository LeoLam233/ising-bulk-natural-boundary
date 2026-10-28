import IsingBulk.HT22.Far.ConstantBudget
import IsingBulk.HT22.Kernel.ActualJets
import IsingBulk.HT22.Transport.FieldNeighborhood.UniformFrameBudget
import IsingBulk.HT22.Tail.ActualCollisionChart
import IsingBulk.HT22.SeedFrameConversion.ActualSeed

/-! The actual new odd-bordered far scalar, with no unproved source jet
premises. Geometry is fixed before the derivative budget and particle count. -/
namespace IsingBulk.HT22.Far
noncomputable section
open IsingBulk.Preferred22 IsingBulk.HT22.Tail Set
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

theorem actual_far_scalar_bound (b : PreferredBranchData) (M : ℝ) (hM : 0<M) :
    ∃ cap₀ : ℝ, 0<cap₀ ∧ cap₀<b.alpha ∧
      ∀ B : PreferredCoareaBump b, B.delta<cap₀ →
      ∃ ε₀ τ₀ δB : ℝ, 0<ε₀ ∧ 0<τ₀ ∧ 0<δB ∧ δB<B.delta ∧
      ∀ d₀ : ℝ, 0<d₀ → ∀ rcut : ℝ → ℝ,
      ContDiff ℝ ∞ rcut → Function.Periodic rcut (2*Real.pi) →
      ∀ j : ℕ, ∃ A : ℝ, ∃ L : ℕ, 0<A ∧
      ∀ N : ℕ, 0<N → ∀ ε τ μ r : ℝ,
      0<ε → ε<ε₀ → 0≤τ → τ<τ₀ → d₀≤r → |μ|+r+ε≤M →
      ∀ θ : Fin N → ℝ,
      (∀ i, -δB≤θ i+b.b ∧ θ i≤B.delta) →
      (∀ i, μ-2*r≤θ i+b.b ∧ θ i+b.b≤μ+2*r) →
      ∀ i k : Fin N, (∀ a, θ i≤θ a ∧ θ a≤θ k) → r≤θ k-θ i →
      ‖(2*Real.pi:ℂ)^(N-1)*regularTransportedScalar τ preferredPopulationCutoff B.p B.m rcut j
        (IsingBulk.Branch.radialParameter b.alpha ε) θ‖≤farOrderEnvelope A L N := by
  obtain ⟨capC,hcapC,hcapCa,hchart⟩ := actual_collision_source_chart b
  obtain ⟨capK,hcapK,hcapKa,hkernel⟩ := Kernel.actual_ordinary_kernel_frame_jets b
  obtain ⟨capS,hcapS,hcapSa,hseed⟩ := SeedFrameConversion.actual_normalized_seed_frame_jets b
  obtain ⟨cap,hcap,hcapa,hfield⟩ := actual_mixed_field_uniform_frame_budget_uniform_cap b M hM
  refine ⟨min (min capC (min capK capS)) cap,lt_min (lt_min hcapC (lt_min hcapK hcapS)) hcap,
    ((min_le_left _ _).trans (min_le_left _ _)).trans_lt hcapCa,?_⟩
  intro B hBcap0
  have hBcap := hBcap0.trans_le (min_le_left _ _)
  have hBfield : B.delta<cap := hBcap0.trans_le (min_le_right _ _)
  obtain ⟨c,δ,eC,tC,δC,_hc,heC,htC,hδC,hδCB,hchart⟩ := hchart B
    (hBcap.trans_le (min_le_left _ _))
  obtain ⟨eK,tK,δK,heK,htK,hδK,hδKB,hkernel⟩ := hkernel B
    (hBcap.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  obtain ⟨eS,tS,δS,heS,htS,hδS,hδSB,hseed⟩ := hseed B
    (hBcap.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨eF,tF,δF,heF,htF,hδF,hδFB,hfield⟩ := hfield B
  let e := min eC (min eK (min eS eF))
  let t := min tC (min tK (min tS tF))
  let dB := min δC (min δK (min δS δF))
  refine ⟨e,t,dB,lt_min heC (lt_min heK (lt_min heS heF)),
    lt_min htC (lt_min htK (lt_min htS htF)),lt_min hδC (lt_min hδK (lt_min hδS hδF)),
    (min_le_left _ _).trans_lt hδCB,?_⟩
  intro d₀ hd₀ rcut hrcut hrper j
  obtain ⟨As,hAs,hs⟩ := hseed rcut hrcut hrper j
  obtain ⟨Ak,hAk,hk⟩ := hkernel j
  obtain ⟨Af,hAf,hf⟩ := hfield j
  let E := max 1 (Real.sqrt M/d₀)
  let R := max 1 (max As (max Ak (Af*E^(j+1))))
  have hR : 1≤R := le_max_left _ _
  have hRpos : 0<R := zero_lt_one.trans_le hR
  have hsR : As≤R := (le_max_left _ _).trans (le_max_right _ _)
  have hkR : Ak≤R := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hfR : Af*E^(j+1)≤R := (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  let A := (preferredCoefficientCountConstant j:ℝ)*R^(2*j+2)*R*(4*Real.exp 1)
  have hA : 0<A := by
    have hc : (0:ℝ)<preferredCoefficientCountConstant j := by exact_mod_cast preferredCoefficientCountConstant_pos j
    dsimp [A]
    positivity
  let L := (j*j+6*j)+(2*j+2)*(2*j+1)+3*j+1
  refine ⟨(2:ℝ)^j*A,L,by positivity,?_⟩
  intro N hN ε τ μ r hε hεr hτ hτr hr hTM θ hθ hwindow i k hext hgap
  have hr0 : 0<r := hd₀.trans_le hr
  have heps : ε<eC ∧ ε<eK ∧ ε<eS ∧ ε<eF := by simpa only [e,lt_min_iff] using hεr
  have htaus : τ<tC ∧ τ<tK ∧ τ<tS ∧ τ<tF := by simpa only [t,lt_min_iff] using hτr
  have hds : dB≤δC ∧ dB≤δK ∧ dB≤δS ∧ dB≤δF := by
    dsimp only [dB]
    exact ⟨min_le_left _ _,(min_le_right _ _).trans (min_le_left _ _),
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)),
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))⟩
  have hbox (d : ℝ) (hd : dB≤d) (a : Fin N) : -d≤θ a+b.b ∧ θ a+b.b≤b.b+B.delta := by
    have hh := (hθ a).2
    constructor <;> linarith [(hθ a).1]
  have hboxF (a : Fin N) : -δF≤θ a+b.b ∧ θ a≤min cap B.delta :=
    ⟨by linarith [(hθ a).1,hds.2.2.2],le_min ((hθ a).2.trans hBfield.le) (hθ a).2⟩
  obtain ⟨Ω,hΩ,hz,hpoint,hRcov,_hregular⟩ := hchart N hN ε τ μ r hε heps.1 hτ htaus.1 hr0
    θ (hbox δC hds.1) hwindow i k hext hgap
  have hsb (xs : List (Option (Fin N))) (hxs : xs.length≤j) :=
    (hs N hN ε τ hε heps.2.2.1 hτ htaus.2.2.1 θ (hbox δS hds.2.2.1) xs hxs).trans
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by linarith) hsR N) (by positivity))
  have hkb (ij : Fin N × Fin N) (xs : List (Option (Fin N))) (hxs : xs.length≤j) :=
    (hk N hN ε τ hε heps.2.1 hτ htaus.2.1 θ (hbox δK hds.2.1) xs hxs ij.1 ij.2).trans hkR
  have hfb (a : Fin N) (xs : List (Option (Fin N))) (hxs : xs.length≤j) :
      ‖frameJet τ B.p B.m (fun t x => residualField t (sourceCoordinate τ B.p B.m t x) a)
        xs (IsingBulk.Branch.radialParameter b.alpha ε) θ‖≤R*(N:ℝ)^(2*j+2)/(1:ℝ)^(1+xs.length) := by
    have hh := hf N hN ε τ μ r hε heps.2.2.2 hτ htaus.2.2.2 hr0 hTM θ hboxF hwindow i k hext hgap xs hxs a
    have habs := far_field_total_jet_bound hAf.le (by positivity : 0< |μ|+r+ε) hTM hd₀ hr
      N (2*j+2) j xs.length hxs
    simpa only [one_pow,div_one] using (hh.trans habs).trans (mul_le_mul_of_nonneg_right hfR (by positivity))
  have hh := regularTransportedScalar_far_of_source_frames hN τ δ preferredPopulationCutoff B.p B.m rcut
    preferredPopulationCutoff_smooth B.smooth B.m_smooth hrcut Ω hΩ hpoint hRcov
    (IsingBulk.Branch.radialParameter b.alpha ε) θ hz R 1 1 hR (by norm_num) le_rfl le_rfl
    1 le_rfl (by norm_num) (j*j+6*j) (2*j+2) j hsb hfb hkb
  simp only [one_pow,mul_one] at hh
  exact hh.trans (farOrderEnvelope_absorb_factor hA.le (one_le_pow₀ (by norm_num)) hN L)

end
end IsingBulk.HT22.Far
