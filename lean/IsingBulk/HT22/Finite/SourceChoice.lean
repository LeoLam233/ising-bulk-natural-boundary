import IsingBulk.HT22.Finite.ComponentChoice
import IsingBulk.HT22.Finite.RemainderObservable
import IsingBulk.HT22.Tail.LocalizedActualBound
import IsingBulk.Preferred22.RightCutoff
namespace IsingBulk.HT22.Finite
noncomputable section
open Set Filter IsingBulk.Preferred22 Physical Physical.FiniteAssembly Geometry Selected
open scoped Topology BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/-- One actual canonical bump, cutoff and fixed contour simultaneously
satisfy all finite selected/anchor estimates and every genuinely separated
localized right remainder bound. The positive epsilon regime precedes N,j
and every partition weight. -/
theorem actual_finite_source_choice (d : PreferredBranchData) {g : ℝ} (hg : 0<g) :
    ∃ B : PreferredCoareaBump d,∃ δ τ e : ℝ,∃ r : ℝ → ℝ,
    0<δ ∧ δ≤g/4 ∧ 0<τ ∧ 0<e ∧ PreferredRightCutoffData d B δ r ∧
    (∀ j : ℕ,∃ C : ℝ,0<C ∧ ∀ negative : Bool,∀ k : ℕ,∀ ε : ℝ,0<ε → ε<e →
      ‖iteratedDeriv j (selectedIntegral negative (2*(k+1)) τ B.p B.m)
        (IsingBulk.Branch.radialParameter d.alpha ε)‖≤C ∧
      Anchor.derivativeMass negative k τ B.p B.m r j (IsingBulk.Branch.radialParameter d.alpha ε)≤C) ∧
    (∀ negative : Bool,∀ n : ℕ,Odd (n+1) → 3≤n+1 →
      ∀ rem : (Fin n → ℝ) → ℝ,ContDiff ℝ ∞ rem →
      (∃ R : ℝ,0<R ∧ ∀ θ∈signedRightRegion (constraintAngle negative) d B δ,rem θ≠0 →
        R<preferredAngularDiameter (preferredLiftedAngles B.delta (constrainedAtTotal (constraintAngle negative) θ))) →
      ∀ j : ℕ,∃ C : ℝ,0<C ∧ ∀ ε : ℝ,0<ε → ε<e →
      ‖iteratedDeriv j (localizedRightIntegral negative n τ B.p B.m r rem)
        (IsingBulk.Branch.radialParameter d.alpha ε)‖≤C*(1+|Real.log ε|)) := by
  obtain ⟨cA,hcA,_,hA⟩ := actual_nonright_component_choice d
  obtain ⟨cR,hcR,_,hR⟩ := Tail.actual_localized_derivative_bound d
  let cap := min cA cR
  have hcap : 0<cap := lt_min hcA hcR
  let B := cappedCanonicalPreferredBump d cap hcap
  have hB : B.delta<cR := (cappedCanonicalPreferredBump_delta_lt d hcap).trans_le (min_le_right _ _)
  obtain ⟨eR,tR,δR,heR,htR,hδR,_,hR⟩ := hR B hB
  let δ := min δR (min (g/4) (preferredRightMargin d B))/2
  have hδ : 0<δ := by dsimp [δ];positivity [(preferredRightMargin_bounds d B).1]
  have hδR' : δ≤δR := by dsimp [δ];linarith [min_le_left δR (min (g/4) (preferredRightMargin d B))]
  have hδg : δ≤g/4 := by
    have hh := (min_le_right δR (min (g/4) (preferredRightMargin d B))).trans (min_le_left _ _)
    dsimp [δ];linarith
  have hδM : δ≤preferredRightMargin d B := by
    have hh := (min_le_right δR (min (g/4) (preferredRightMargin d B))).trans (min_le_right _ _)
    dsimp [δ];linarith [(preferredRightMargin_bounds d B).1]
  let r := preferredRightCutoff d δ
  have hcut : PreferredRightCutoffData d B δ r := preferred_right_cutoff_data_of_le d B hδ hδM
  obtain ⟨eA,τ,heA,hτ,hτR,hA⟩ := hA cap hcap (min_le_left _ _) δ tR hδ htR
  let e := min eA eR
  have he : 0<e := lt_min heA heR
  refine ⟨B,δ,τ,e,r,hδ,hδg,hτ,he,hcut,?_,?_⟩
  · intro j
    obtain ⟨C,hC,hA⟩ := hA r hcut j
    exact ⟨C,hC,fun negative k ε hε hεe => hA negative k ε hε (hεe.trans_le (min_le_left _ _))⟩
  · intro negative n hn hn3 rem hrem hsep j
    obtain ⟨k,hk⟩ : ∃k : ℕ,n=2*k+2 := by
      obtain ⟨q,hq⟩ := hn
      exact ⟨q-1,by omega⟩
    subst n
    obtain ⟨R,hRpos,hsep⟩ := hsep
    let W := separatedAmbientRemainder R rem
    let ρ := R/(2*((2*k+3:ℕ):ℝ))
    have hρ : 0<ρ := by dsimp [ρ];positivity
    have hW : ContDiff ℝ ∞ W := separatedAmbientRemainder_smooth R rem hrem
    have hWzero : ∀ x,preferredAngularDiameter x<ρ → W=ᶠ[𝓝 x] fun _ => 0 := by
      intro x hx
      exact separatedAmbientRemainder_zero_germ_small hRpos rem x hx
    obtain ⟨C,hC,hbound⟩ := hR δ hδR' r hcut k W hW ρ hρ hWzero j
    refine ⟨C,hC,?_⟩
    intro ε hε hεe
    rw [separated_remainder_eq_observable negative (2*k+2) d B hRpos τ r hcut rem hsep]
    exact hbound negative ε τ hε (hεe.trans_le (min_le_right _ _)) hτ.le hτR
end
end IsingBulk.HT22.Finite
