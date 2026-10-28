import IsingBulk.HT22.Transport.FieldNeighborhood.ActualScaleJets
import IsingBulk.HT22.Transport.FieldNeighborhood.FixedVFrameDomain
import IsingBulk.Preferred22.SourceFrameGeometry

/-! Full actual fixed-v field frame jets, with real smooth bumps and
all particle numbers. All geometric source inputs are discharged. -/
namespace IsingBulk.HT22
noncomputable section
open Set Geometry IsingBulk.Preferred22 IsingBulk.HT22.Tail
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem actual_mixed_field_frame_jets (b : PreferredBranchData)
    (B : PreferredCoareaBump b) (M : ℝ) (hM : 0<M) :
    ∃ cap C ε₀ τ₀ δB η c K : ℝ,
      0<cap ∧ cap<b.alpha ∧ 0<C ∧ 0<ε₀ ∧ 0<τ₀ ∧ 0<δB ∧ δB<B.delta ∧
      0<η ∧ 0<c ∧ 1≤K ∧
      ∀ N : ℕ, 0<N → ∀ ε τ μ r : ℝ,
      0<ε → ε<ε₀ → 0≤τ → τ<τ₀ → 0<r → |μ|+r+ε≤M →
      ∀ θ : Fin N → ℝ,
      (∀ i, -δB≤θ i+b.b ∧ θ i≤min cap B.delta) →
      (∀ i, μ-2*r≤θ i+b.b ∧ θ i+b.b≤μ+2*r) →
      ∀ i j : Fin N, (∀ a, θ i≤θ a ∧ θ a≤θ j) → r≤θ j-θ i →
      ∀ xs : List (Option (Fin N)), ∀ a : Fin N,
      ‖frameJet τ B.p B.m (fun t x => sourceResidual t (sourceCoordinate τ B.p B.m t x) a)
        xs (IsingBulk.Branch.radialParameter b.alpha ε) θ‖≤
        (cauchyJetConstant xs.length*(1296*C^2/c)/η^xs.length)*(N:ℝ)^(2*xs.length+2)/
          (K*r/Real.sqrt (|μ|+r+ε))^(xs.length+1) := by
  obtain ⟨cap,C,e,t,δB,η,c,K,hcap,hcapa,hC,he,ht,hδB,hδBB,hη,hc,hK,hjets⟩ :=
    actual_mixed_field_scale_jets b B M hM
  obtain ⟨δ,ef,tf,_hδ,_hδa,hef,htf,hpoints⟩ := preferred_actual_frame_points b B
  refine ⟨cap,C,min e ef,min t tf,δB,η,c,K,hcap,hcapa,hC,lt_min he hef,
    lt_min ht htf,hδB,hδBB,hη,hc,hK,?_⟩
  intro N hN ε τ μ r hε hε₀ hτ hτ₀ hr hTM θ hθ hwindow i j hext hgap xs a
  obtain ⟨hne,hbound⟩ := hjets N hN ε τ μ r hε (hε₀.trans_le (min_le_left _ _))
    hτ (hτ₀.trans_le (min_le_left _ _)) hr hTM θ hθ hwindow i j hext hgap
  have hbox (a : Fin N) : -δB≤θ a+b.b ∧ θ a+b.b≤b.b+B.delta := by
    have hh := (hθ a).2.trans (min_le_right _ _)
    exact ⟨(hθ a).1,by linarith⟩
  obtain ⟨hpoint,hinterior⟩ := hpoints δB hδB hδBB N hN ε τ hε
    (hε₀.trans_le (min_le_right _ _)) hτ (hτ₀.trans_le (min_le_right _ _)) θ hbox
  have ha := sourceResidual_analyticAt (IsingBulk.Branch.radialParameter b.alpha ε)
    (sourceCoordinate τ B.p B.m (IsingBulk.Branch.radialParameter b.alpha ε) θ)
    (fun i => framePoint_inverse_analytic hpoint i) hne
  exact residual_frameJet_bound τ δ B.p B.m B.smooth (B.smooth.comp contDiff_neg)
    (IsingBulk.Branch.radialParameter b.alpha ε) θ hpoint hinterior ha xs _
    ((norm_nonneg _).trans (hbound xs.length)) (hbound xs.length) a

theorem actual_mixed_field_frame_jets_uniform_cap (b : PreferredBranchData)
    (M : ℝ) (hM : 0<M) :
    ∃ cap : ℝ, 0<cap ∧ cap<b.alpha ∧ ∀ B : PreferredCoareaBump b,
    ∃ C ε₀ τ₀ δB η c K : ℝ,
      0<C ∧ 0<ε₀ ∧ 0<τ₀ ∧ 0<δB ∧ δB<B.delta ∧
      0<η ∧ 0<c ∧ 1≤K ∧
      ∀ N : ℕ, 0<N → ∀ ε τ μ r : ℝ,
      0<ε → ε<ε₀ → 0≤τ → τ<τ₀ → 0<r → |μ|+r+ε≤M →
      ∀ θ : Fin N → ℝ,
      (∀ i, -δB≤θ i+b.b ∧ θ i≤min cap B.delta) →
      (∀ i, μ-2*r≤θ i+b.b ∧ θ i+b.b≤μ+2*r) →
      ∀ i j : Fin N, (∀ a, θ i≤θ a ∧ θ a≤θ j) → r≤θ j-θ i →
      ∀ xs : List (Option (Fin N)), ∀ a : Fin N,
      ‖frameJet τ B.p B.m (fun t x => sourceResidual t (sourceCoordinate τ B.p B.m t x) a)
        xs (IsingBulk.Branch.radialParameter b.alpha ε) θ‖≤
        (cauchyJetConstant xs.length*(1296*C^2/c)/η^xs.length)*(N:ℝ)^(2*xs.length+2)/
          (K*r/Real.sqrt (|μ|+r+ε))^(xs.length+1) := by
  obtain ⟨cap,hcap,hcapa,hsource⟩ := actual_mixed_field_scale_jets_uniform_cap b M hM
  refine ⟨cap,hcap,hcapa,?_⟩
  intro B
  obtain ⟨C,e,t,δB,η,c,K,hC,he,ht,hδB,hδBB,hη,hc,hK,hjets⟩ :=
    hsource B
  obtain ⟨δ,ef,tf,_hδ,_hδa,hef,htf,hpoints⟩ := preferred_actual_frame_points b B
  refine ⟨C,min e ef,min t tf,δB,η,c,K,hC,lt_min he hef,
    lt_min ht htf,hδB,hδBB,hη,hc,hK,?_⟩
  intro N hN ε τ μ r hε hε₀ hτ hτ₀ hr hTM θ hθ hwindow i j hext hgap xs a
  obtain ⟨hne,hbound⟩ := hjets N hN ε τ μ r hε (hε₀.trans_le (min_le_left _ _))
    hτ (hτ₀.trans_le (min_le_left _ _)) hr hTM θ hθ hwindow i j hext hgap
  have hbox (a : Fin N) : -δB≤θ a+b.b ∧ θ a+b.b≤b.b+B.delta := by
    have hh := (hθ a).2.trans (min_le_right _ _)
    exact ⟨(hθ a).1,by linarith⟩
  obtain ⟨hpoint,hinterior⟩ := hpoints δB hδB hδBB N hN ε τ hε
    (hε₀.trans_le (min_le_right _ _)) hτ (hτ₀.trans_le (min_le_right _ _)) θ hbox
  have ha := sourceResidual_analyticAt (IsingBulk.Branch.radialParameter b.alpha ε)
    (sourceCoordinate τ B.p B.m (IsingBulk.Branch.radialParameter b.alpha ε) θ)
    (fun i => framePoint_inverse_analytic hpoint i) hne
  exact residual_frameJet_bound τ δ B.p B.m B.smooth (B.smooth.comp contDiff_neg)
    (IsingBulk.Branch.radialParameter b.alpha ε) θ hpoint hinterior ha xs _
    ((norm_nonneg _).trans (hbound xs.length)) (hbound xs.length) a

end
end IsingBulk.HT22
