import IsingBulk.Tail.MixedActivePairJets

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

theorem mixed_actual_pair_coordinate_bounds (d : LocalBranchData) :
    ∃ e t₀ : ℝ,0<e ∧ 0<t₀ ∧ ∀ (f : SelectorFunctions),
      (∀ x,0≤f.p x ∧ f.p x≤1) → (∀ x,0≤f.m x ∧ f.m x≤1) →
      ∀ (N : ℕ) (eps τ lam : ℝ) (θ : Fin N → ℝ) (i : Fin N) (s : ℂ),
      1≤N → 0≤eps → eps≤e → 0≤τ → 0≤lam → lam≤1 → lam*τ≤t₀ →
      ‖s-radialParameter d.theta eps‖≤(1/4:ℝ)*eps →
      ‖s‖≤2 ∧ ‖deformedPoint f (Real.exp (-d.c₀*eps)) τ lam θ i‖≤2 := by
  obtain ⟨e,t₀,he,ht,hMotion⟩ := mixed_actual_pair_tube_motion d (δ := 1) zero_lt_one
  refine ⟨e,t₀,he,ht,?_⟩
  intro f hp hm N eps τ lam θ i s hN heps hepsle hτ hl0 hl1 htl hs
  have hh := hMotion f hp hm N eps τ lam θ i s hN heps hepsle hτ hl0 hl1 htl hs
  constructor
  · have hb := norm_le_norm_sub_add s (radialParameter d.theta 0)
    rw [radialParameter_norm (by norm_num)] at hb
    linarith
  · have hb := norm_le_norm_sub_add (deformedPoint f (Real.exp (-d.c₀*eps)) τ lam θ i) (limitingAngle (θ i))
    rw [limitingAngle_norm] at hb
    linarith

theorem mixed_actual_active_compact_pair_jets (d : LocalBranchData) (inner : ℝ) (hi : 0< inner) (order : ℕ) :
    ∃ e t₀ C : ℝ,0<e ∧ 0<t₀ ∧ 0<C ∧ ∀ (f : SelectorFunctions),
      (∀ x,0≤f.p x ∧ f.p x≤1) → (∀ x,0≤f.m x ∧ f.m x≤1) →
      ∀ (N : ℕ) (eps τ lam : ℝ) (θ : Fin N → ℝ) (q i j : Fin N) (s : ℂ),
      1≤N → 0≤eps → eps≤e → 0≤τ → 0≤lam → lam≤1 → lam*τ≤t₀ → θ∈angleBox N →
      inner/2≤|sectorDisplacement d.thetaB (θ i)| → inner/2≤|sectorDisplacement d.thetaB (θ j)| →
      ‖s-radialParameter d.theta eps‖≤(1/4:ℝ)*eps →
      let y := deformedPoint f (Real.exp (-d.c₀*eps)) τ lam θ
      AnalyticAt ℂ (activeCompactPair q i j s (y i) (y j)) 0 ∧ ∀ k≤order,
      ‖iteratedFDeriv ℂ k (activeCompactPair q i j s (y i) (y j)) 0‖≤C := by
  obtain ⟨eP,tP,B,heP,htP,hB,hPair⟩ := mixed_actual_compact_pair_jets d inner hi order
  obtain ⟨eM,tM,heM,htM,hBounds⟩ := mixed_actual_pair_coordinate_bounds d
  obtain ⟨C,hC,hActive⟩ := active_pair_jets_of_scalar 2 B hB order
  refine ⟨min eP eM,min tP tM,C,lt_min heP heM,lt_min htP htM,hC,?_⟩
  intro f hp hm N eps τ lam θ q i j s hN heps hepsle hτ hl0 hl1 htl hθ hiP hjP hs
  obtain ⟨ha,hj⟩ := hPair f hp hm N eps τ lam θ i j s hN heps
    (hepsle.trans (min_le_left _ _)) hτ hl0 hl1 (htl.trans (min_le_left _ _)) hθ hiP hjP hs
  have hiB := hBounds f hp hm N eps τ lam θ i s hN heps
    (hepsle.trans (min_le_right _ _)) hτ hl0 hl1 (htl.trans (min_le_right _ _)) hs
  have hjB := hBounds f hp hm N eps τ lam θ j s hN heps
    (hepsle.trans (min_le_right _ _)) hτ hl0 hl1 (htl.trans (min_le_right _ _)) hs
  let y := deformedPoint f (Real.exp (-d.c₀*eps)) τ lam θ
  have hpTuple : ‖(s,y i,y j)‖≤2 := by
    simpa only [Prod.norm_def] using max_le hiB.1 (max_le hiB.2 hjB.2)
  exact (hActive N i q j (s,y i,y j) hpTuple).2 ha hj


theorem mixed_actual_active_branch_compact_pair_jets (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) (cap : ℝ) (hcap : 0<cap) (order : ℕ) :
    ∃ inner₀ : ℝ,0< inner₀ ∧ inner₀≤cap ∧ ∀ inner : ℝ,0< inner → inner≤ inner₀ →
      ∃ c e t₀ C : ℝ,0<c ∧ 0<e ∧ 0<t₀ ∧ 0<C ∧
      ∀ η α : ℝ,0<η → η≤Real.sin d.thetaB/4 → 0<α →
      ∀ (N : ℕ) (eps τ lam : ℝ) (θ : Fin N → ℝ) (j q k : Fin N) (s : ℂ),
      1≤N → 0<eps → eps<e → 0≤τ → 0≤lam → lam≤1 → lam*τ<t₀ →
      |sectorDisplacement d.thetaB (θ j)|≤ inner →
      θ k∈Icc 0 (2*Real.pi) → inner/2≤|sectorDisplacement d.thetaB (θ k)| →
      ‖s-radialParameter d.theta eps‖≤c*eps →
      let y := deformedPoint (constructedSelector d.thetaB η α) (Real.exp (-d.c₀*eps)) τ lam θ
      let φ := mixedSourcePhase s (y j)
      AnalyticAt ℂ (activeBranchCompactPair j q k s φ (y k)) 0 ∧ ∀ l≤order,
      ‖iteratedFDeriv ℂ l (activeBranchCompactPair j q k s φ (y k)) 0‖≤C := by
  let U : Set (ℂ × ℂ) := {p | ‖p.2‖<1}
  have hU : IsOpen U := isOpen_lt (continuous_snd.norm) continuous_const
  have hbase : (radialParameter d.theta 0,(0:ℂ))∈U := by simp [U]
  obtain ⟨iB,cB,eB,tB,hiB,hiCap,hcB,heB,htB,hBranch⟩ :=
    mixed_actual_branch_chart_neighborhood d hcsmall U hU hbase cap hcap
  obtain ⟨inner₀,hi₀,hiiB,hPair⟩ := mixed_actual_branch_compact_pair_jets_below_cap d hcsmall iB hiB order
  refine ⟨inner₀,hi₀,hiiB.trans hiCap,?_⟩
  intro inner hi hinner
  obtain ⟨cP,eP,tP,B,hcP,heP,htP,hB,hPair⟩ := hPair inner hi hinner
  obtain ⟨eM,tM,heM,htM,hBounds⟩ := mixed_actual_pair_coordinate_bounds d
  obtain ⟨C,hC,hActive⟩ := active_pair_jets_of_scalar 2 B hB order
  refine ⟨min cP (min cB (1/4)),min eP (min eB eM),min tP (min tB tM),C,
    lt_min hcP (lt_min hcB (by norm_num)),lt_min heP (lt_min heB heM),
    lt_min htP (lt_min htB htM),hC,?_⟩
  intro η α hη hηsmall hα N eps τ lam θ j q k s hN heps hepslt hτ hl0 hl1 htl hprofile hθk hkP hs
  let f := constructedSelector d.thetaB η α
  let y := deformedPoint f (Real.exp (-d.c₀*eps)) τ lam θ
  let φ := mixedSourcePhase s (y j)
  obtain ⟨ha,hj⟩ := hPair η α hη hηsmall hα N eps τ lam θ j k s hN heps
    (hepslt.trans_le (min_le_left _ _)) hτ hl0 hl1 (htl.trans_le (min_le_left _ _)) hprofile hθk hkP
    (hs.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) heps.le))
  have hφ : ‖φ‖<1 := hBranch η α hη hηsmall hα N eps τ lam θ j s hN heps
    (hepslt.trans_le ((min_le_right _ _).trans (min_le_left _ _))) hτ hl0 hl1
    (htl.trans_le ((min_le_right _ _).trans (min_le_left _ _))) (hprofile.trans (hinner.trans hiiB))
    (hs.trans (mul_le_mul_of_nonneg_right ((min_le_right _ _).trans (min_le_left _ _)) heps.le))
  have hbound := hBounds f (fun x => thresholdStep_range _ _ _)
    (fun x => ⟨Real.smoothTransition.nonneg _,Real.smoothTransition.le_one _⟩)
    N eps τ lam θ k s hN heps.le
    (hepslt.le.trans ((min_le_right _ _).trans (min_le_right _ _))) hτ hl0 hl1
    (htl.le.trans ((min_le_right _ _).trans (min_le_right _ _)))
    (hs.trans (mul_le_mul_of_nonneg_right ((min_le_right _ _).trans (min_le_right _ _)) heps.le))
  have hp : ‖(s,φ,y k)‖≤2 := by
    simpa only [Prod.norm_def] using max_le hbound.1 (max_le (by linarith : ‖φ‖≤2) hbound.2)
  exact (hActive N j q k (s,φ,y k) hp).1 ha hj

end
end IsingBulk.Tail
