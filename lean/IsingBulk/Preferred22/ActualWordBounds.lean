import IsingBulk.Preferred22.ActualSeedFrames
import IsingBulk.Preferred22.SourceCoefficientBounds

/-! Actual complete-right scalar word coefficient bounds. Every new
analytic/frame/cutoff/minor input is proved in the source chain. -/
namespace IsingBulk.Preferred22
noncomputable section
open scoped BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false

theorem preferred_actual_normalized_word_bounds (d : PreferredBranchData) :
    ∃ cap : ℝ, 0<cap ∧ cap<d.alpha ∧
      ∀ B : PreferredCoareaBump d, B.delta<cap →
      ∃ ε₀ τ₀ δB : ℝ, 0<ε₀ ∧ 0<τ₀ ∧ 0<δB ∧ δB<B.delta ∧
        ∀ rcut : ℝ → ℝ, ContDiff ℝ ∞ rcut → Function.Periodic rcut (2*Real.pi) →
        ∀ j : ℕ, ∃ C : ℝ, 0<C ∧
        ∀ N : ℕ, 0<N → ∀ ε τ : ℝ, 0<ε → ε<ε₀ → 0≤τ → τ<τ₀ →
        ∀ θ : Fin N → ℝ,
        (∀ i, -δB≤θ i+d.b ∧ θ i+d.b≤d.b+B.delta) →
        0<preferredAngularDiameter θ → ∀ w : PreferredMarkedWord N j,
        ‖((N.factorial:ℂ)*(2*Real.pi:ℂ)^(N-1))*
          preferredWordCoefficient τ preferredPopulationCutoff B.p B.m rcut j w
            (IsingBulk.Branch.radialParameter d.alpha ε) θ‖≤
          C^N*(N:ℝ)^(5*j*j+12*j+2)/preferredAngularDiameter θ^(preferredWordLoss j w) := by
  obtain ⟨capS,hcapS,hcapSa,hseeds⟩ := preferred_actual_normalized_seed_frame_jets d
  obtain ⟨capW,hcapW,hcapWa,hwords⟩ := preferred_actual_word_bound_of_seed d
  refine ⟨min capS capW,lt_min hcapS hcapW,(min_le_left _ _).trans_lt hcapSa,?_⟩
  intro B hBcap
  obtain ⟨εS,τS,δS,hεS,hτS,hδS,hδSB,hS⟩ := hseeds B (hBcap.trans_le (min_le_left _ _))
  obtain ⟨εW,τW,δW,hεW,hτW,hδW,hδWB,hW⟩ := hwords B (hBcap.trans_le (min_le_right _ _))
  let δB := min δS δW
  refine ⟨min εS εW,min τS τW,δB,lt_min hεS hεW,lt_min hτS hτW,
    lt_min hδS hδW,(min_le_left _ _).trans_lt hδSB,?_⟩
  intro rcut hrcut hrper j
  obtain ⟨A,hA,hseed⟩ := hS rcut hrcut hrper j
  obtain ⟨C,hC,hword⟩ := hW j A hA (j*j+5*j)
  refine ⟨C,hC,?_⟩
  intro N hN ε τ hε hεr hτ hτr θ hθ hdiam w
  have hθS (i : Fin N) : -δS≤θ i+d.b ∧ θ i+d.b≤d.b+B.delta :=
    ⟨(neg_le_neg (min_le_left _ _)).trans (hθ i).1,(hθ i).2⟩
  have hθW (i : Fin N) : -δW≤θ i+d.b ∧ θ i+d.b≤d.b+B.delta :=
    ⟨(neg_le_neg (min_le_right _ _)).trans (hθ i).1,(hθ i).2⟩
  have hh := hword preferredPopulationCutoff rcut preferredPopulationCutoff_smooth hrcut N hN ε τ hε
    (hεr.trans_le (min_le_right _ _)) hτ (hτr.trans_le (min_le_right _ _)) θ hθW hdiam
    (fun xs hxs => hseed N hN ε τ hε (hεr.trans_le (min_le_left _ _)) hτ
      (hτr.trans_le (min_le_left _ _)) θ hθS xs hxs) w
  convert hh using 1
  congr 2
  ring

end
end IsingBulk.Preferred22
