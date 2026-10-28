import IsingBulk.HT22.Selected.AllOddBound
import IsingBulk.HT22.Anchor.AbsoluteSummation
namespace IsingBulk.HT22.Finite
noncomputable section
open IsingBulk.Preferred22 IsingBulk.HT22.Selected
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Common actual selected/anchor choices, allowing any smaller externally
specified cap, any actual right margin, and any positive external contour
upper bound. The contour and epsilon regime precede all derivative and odd
particle orders. -/
theorem actual_nonright_component_choice (d : PreferredBranchData) :
    ∃ capA : ℝ,0<capA ∧ capA<d.alpha ∧ ∀ cap : ℝ,∀ hcap : 0<cap,cap≤capA →
    ∀ δ t : ℝ,0<δ → 0<t →
    let B := cappedCanonicalPreferredBump d cap hcap
    ∃ e τ : ℝ,0<e ∧ 0<τ ∧ τ<t ∧
    ∀ r : ℝ → ℝ,PreferredRightCutoffData d B δ r → ∀ j : ℕ,
    ∃ C : ℝ,0<C ∧ ∀ negative : Bool,∀ k : ℕ,∀ ε : ℝ,0<ε → ε<e →
    ‖iteratedDeriv j (selectedIntegral negative (2*(k+1)) τ B.p B.m)
      (IsingBulk.Branch.radialParameter d.alpha ε)‖≤C ∧
    Anchor.derivativeMass negative k τ B.p B.m r j (IsingBulk.Branch.radialParameter d.alpha ε)≤C := by
  obtain ⟨capA,hcapA,hcapAa,hA⟩ := Anchor.actual_anchor_absolute_majorant d
  refine ⟨capA,hcapA,hcapAa,?_⟩
  intro cap hcap hcapA' δ t hδ ht
  let B := cappedCanonicalPreferredBump d cap hcap
  have hB : B.delta<capA := (cappedCanonicalPreferredBump_delta_lt d hcap).trans_le hcapA'
  obtain ⟨eA,tA,heA,htA,hA⟩ := hA B hB δ hδ
  obtain ⟨ρ,hρ,_,hF⟩ := selected_all_odd_bound d hcap
  let τ := min t (min tA ρ)/2
  have hτ : 0<τ := by dsimp [τ];positivity
  have hτt : τ<t := by dsimp [τ];linarith [min_le_left t (min tA ρ)]
  have hτA : τ<tA := by
    have hh := (min_le_right t (min tA ρ)).trans (min_le_left _ _)
    dsimp [τ];linarith
  have hτρ : τ<ρ := by
    have hh := (min_le_right t (min tA ρ)).trans (min_le_right _ _)
    dsimp [τ];linarith
  refine ⟨min eA ρ,τ,lt_min heA hρ,hτ,hτt,?_⟩
  intro r hcut j
  obtain ⟨CA,hCA,hAs,hA⟩ := hA r hcut j
  obtain ⟨CF,hCF,hF⟩ := hF τ hτ hτρ j
  let MA := ∑' k,Anchor.oddAnchorEnvelope CA j k
  have he0 (k : ℕ) : 0≤Anchor.oddAnchorEnvelope CA j k := by
    unfold Anchor.oddAnchorEnvelope shellOrderEnvelope;positivity
  have hMA : 0≤MA := tsum_nonneg he0
  refine ⟨CF+MA+1,by positivity,?_⟩
  intro negative k ε hε hεe
  constructor
  · exact (hF negative (k+1) (by omega) ε hε (hεe.trans_le (min_le_right _ _))).trans (by linarith)
  · have hh := hA negative k ε τ hε (hεe.trans_le (min_le_left _ _)) hτ.le hτA j le_rfl
    have hk : Anchor.oddAnchorEnvelope CA j k≤MA := hAs.le_tsum k (fun k _ => he0 k)
    exact (hh.trans hk).trans (by linarith)
end
end IsingBulk.HT22.Finite
