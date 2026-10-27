import IsingBulk.Preferred22.SeedFrameBound
import IsingBulk.Preferred22.SourceCutoffFrameJets

/-! Fully source-specific normalized seed jets, retaining the original
population cutoff, right cutoff, occupancy dependence and factorial. -/
namespace IsingBulk.Preferred22
noncomputable section
open scoped BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false

theorem preferred_actual_normalized_seed_frame_jets (d : PreferredBranchData) :
    ∃ cap : ℝ, 0<cap ∧ cap<d.alpha ∧
      ∀ B : PreferredCoareaBump d, B.delta<cap →
      ∃ ε₀ τ₀ δB : ℝ, 0<ε₀ ∧ 0<τ₀ ∧ 0<δB ∧ δB<B.delta ∧
        ∀ rcut : ℝ → ℝ, ContDiff ℝ ∞ rcut → Function.Periodic rcut (2*Real.pi) →
        ∀ j : ℕ, ∃ A : ℝ, 1≤A ∧
        ∀ N : ℕ, 0<N → ∀ ε τ : ℝ, 0<ε → ε<ε₀ → 0≤τ → τ<τ₀ →
        ∀ θ : Fin N → ℝ,
        (∀ i, -δB≤θ i+d.b ∧ θ i+d.b≤d.b+B.delta) →
        ∀ xs : List (Option (Fin N)), xs.length≤j →
        ‖((N.factorial:ℂ)*(2*Real.pi:ℂ)^(N-1))*preferredFrameJet τ B.p B.m
          (preferredRegularSeedCoefficient τ preferredPopulationCutoff B.p B.m rcut) xs
          (IsingBulk.Branch.radialParameter d.alpha ε) θ‖≤A^N*(N:ℝ)^(j*j+5*j) := by
  obtain ⟨capW,hcapW,hcapWa,hweights⟩ := preferred_actual_cell_weight_frame_jets d
  obtain ⟨capA,hcapA,hcapAa,hbodies⟩ := preferred_actual_regular_frame_jets d
  refine ⟨min capW capA,lt_min hcapW hcapA,(min_le_left _ _).trans_lt hcapWa,?_⟩
  intro B hBcap
  obtain ⟨εW,τW,δW,hεW,hτW,hδW,hδWB,hW⟩ := hweights B (hBcap.trans_le (min_le_left _ _))
  obtain ⟨εA,τA,δA,hεA,hτA,hδA,hδAB,hA⟩ := hbodies B (hBcap.trans_le (min_le_right _ _))
  obtain ⟨δ,εF,τF,hδ,hδa,hεF,hτF,hframe⟩ := preferred_actual_frame_points d B
  let ε₀ := min εW (min εA εF)
  let τ₀ := min τW (min τA τF)
  let δB := min δW δA
  have hδB : 0<δB := lt_min hδW hδA
  have hδBB : δB<B.delta := (min_le_left _ _).trans_lt hδWB
  refine ⟨ε₀,τ₀,δB,lt_min hεW (lt_min hεA hεF),lt_min hτW (lt_min hτA hτF),hδB,hδBB,?_⟩
  intro rcut hrcut hrper j
  obtain ⟨Cw,hCw,hwbound⟩ := hW rcut hrcut hrper j
  obtain ⟨Ca,hCa,habound⟩ := hA j
  let Ca' := max 1 Ca
  have hCa' : 1≤Ca' := le_max_left _ _
  let A := (2:ℝ)^j*Cw*((2:ℝ)^j*Ca')
  have hA' : 1≤A := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) hCw)
    (one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) hCa')
  refine ⟨A,hA',?_⟩
  intro N hN ε τ hε hεr hτ hτr θ hθ xs hxs
  have heW : ε<εW := hεr.trans_le (min_le_left _ _)
  have heA : ε<εA := hεr.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have heF : ε<εF := hεr.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have htW : τ<τW := hτr.trans_le (min_le_left _ _)
  have htA : τ<τA := hτr.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have htF : τ<τF := hτr.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hθW (i : Fin N) : -δW≤θ i+d.b ∧ θ i+d.b≤d.b+B.delta :=
    ⟨(neg_le_neg (min_le_left _ _)).trans (hθ i).1,(hθ i).2⟩
  have hθA (i : Fin N) : -δA≤θ i+d.b ∧ θ i+d.b≤d.b+B.delta :=
    ⟨(neg_le_neg (min_le_right _ _)).trans (hθ i).1,(hθ i).2⟩
  obtain ⟨hpoint,hθstrict⟩ := hframe δB hδB hδBB N hN ε τ hε heF hτ htF θ hθ
  exact preferred_source_seed_frame_bound hN τ δ preferredPopulationCutoff B.p B.m rcut
    preferredPopulationCutoff_smooth B.smooth B.m_smooth hrcut
    (IsingBulk.Branch.radialParameter d.alpha ε) θ hpoint hθstrict j (j*j+5*j) Cw Ca' hCw hCa'
    (fun ys hys => hwbound N hN ε τ hε heW hτ htW θ hθW ys hys)
    (fun i ys hys => ((habound N hN ε τ hε heA hτ htA θ hθA ys hys).1 i).trans (le_max_right _ _))
    xs hxs

end
end IsingBulk.Preferred22
