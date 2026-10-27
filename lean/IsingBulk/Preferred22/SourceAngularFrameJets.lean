import IsingBulk.Preferred22.AngularFrameBounds
import IsingBulk.Preferred22.SourceCutoffFrameJets
import IsingBulk.Preferred22.CollectiveFrameJets

/-! The complete actual collective B and angular V frame bound (7.14).
The deformation regime is fixed before all orders and particle counts. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set Metric
open scoped BigOperators ContDiff Topology Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false

theorem preferred_actual_collective_angular_frame_jets (d : PreferredBranchData) :
    ∃ cap : ℝ, 0<cap ∧ cap<d.alpha ∧
      ∀ B : PreferredCoareaBump d, B.delta<cap →
      ∃ ε₀ τ₀ δB : ℝ, 0<ε₀ ∧ 0<τ₀ ∧ 0<δB ∧ δB<B.delta ∧
        ∀ j : ℕ, ∃ C : ℝ, 0<C ∧
        ∀ N : ℕ, 0<N → ∀ ε τ : ℝ, 0<ε → ε<ε₀ → 0≤τ → τ<τ₀ →
        ∀ θ : Fin N → ℝ,
        (∀ i, -δB≤θ i+d.b ∧ θ i+d.b≤d.b+B.delta) →
        0<preferredAngularDiameter θ →
        ∀ xs : List (Option (Fin N)), xs.length≤j → ∀ i,
        let s := IsingBulk.Branch.radialParameter d.alpha ε
        ‖preferredFrameJet τ B.p B.m
          (fun t x => preferredResidualCollective t (preferredSourceCoordinate τ B.p B.m t x) i) xs s θ‖+
        ‖preferredFrameJet τ B.p B.m (fun t x => preferredSourceAngularField .right τ B.p B.m t x i) xs s θ‖≤
          C*(N:ℝ)^(j*j+5*j+3)/preferredAngularDiameter θ^(1+preferredCoordinateJetOrder xs) := by
  obtain ⟨capB,hcapB,hcapBa,hBj⟩ := preferred_actual_collective_frame_jets d
  obtain ⟨capF,hcapF,hcapFa,hFj⟩ := preferred_actual_angular_frame_control d
  obtain ⟨capA,hcapA,hcapAa,hAn⟩ := preferred_actual_collective_neighborhood d
  refine ⟨min capB (min capF capA),lt_min hcapB (lt_min hcapF hcapA),
    (min_le_left _ _).trans_lt hcapBa,?_⟩
  intro B hBcap
  obtain ⟨εB,τB,δB₁,hεB,hτB,hδB₁,hδB₁B,hBjets⟩ := hBj B (hBcap.trans_le (min_le_left _ _))
  obtain ⟨εF,τF,δB₂,hεF,hτF,hδB₂,hδB₂B,hFjets⟩ :=
    hFj B (hBcap.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  obtain ⟨a,M,εA,τA,δB₃,ha,hM,hεA,hτA,hδB₃,hδB₃B,hneigh⟩ :=
    hAn B (hBcap.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨δ,εG,τG,hδ,hδa,hεG,hτG,hframe⟩ := preferred_actual_frame_points d B
  let ε₀ := min εB (min εF (min εA εG))
  let τ₀ := min τB (min τF (min τA τG))
  let δB := min δB₁ (min δB₂ δB₃)
  have hδB : 0<δB := lt_min hδB₁ (lt_min hδB₂ hδB₃)
  have hδBB : δB<B.delta := (min_le_left _ _).trans_lt hδB₁B
  refine ⟨ε₀,τ₀,δB,lt_min hεB (lt_min hεF (lt_min hεA hεG)),
    lt_min hτB (lt_min hτF (lt_min hτA hτG)),hδB,hδBB,?_⟩
  intro j
  obtain ⟨CB,hCB,hBbound⟩ := hBjets j
  obtain ⟨CF,hCF,hFbound⟩ := hFjets j
  let D := d.b+2*B.delta+1
  have hD : 1≤D := by dsimp [D]; linarith [d.b_pos,B.delta_pos]
  have hDp : 0<D := lt_of_lt_of_le (by norm_num) hD
  have hCFp : 0<CF := lt_of_lt_of_le (by norm_num) hCF
  let CV := (2:ℝ)^j*CF^2*CF*D^(j+1)+((2:ℝ)^j*CF^2*D^j)*((2:ℝ)^j*CF*D^j*CB)
  have hCV : 0<CV := by dsimp [CV]; positivity
  refine ⟨CB+CV,add_pos hCB hCV,?_⟩
  intro N hN ε τ hε hεr hτ hτr θ hθ hdiam xs hxs i
  have heB : ε<εB := hεr.trans_le (min_le_left _ _)
  have heF : ε<εF := hεr.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have heA : ε<εA := hεr.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have heG : ε<εG := hεr.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have htB : τ<τB := hτr.trans_le (min_le_left _ _)
  have htF : τ<τF := hτr.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have htA : τ<τA := hτr.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have htG : τ<τG := hτr.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hθB (k : Fin N) : -δB₁≤θ k+d.b ∧ θ k+d.b≤d.b+B.delta :=
    ⟨(neg_le_neg (min_le_left _ _)).trans (hθ k).1,(hθ k).2⟩
  have hθF (k : Fin N) : -δB₂≤θ k+d.b ∧ θ k+d.b≤d.b+B.delta :=
    ⟨(neg_le_neg ((min_le_right _ _).trans (min_le_left _ _))).trans (hθ k).1,(hθ k).2⟩
  have hθA (k : Fin N) : -δB₃≤θ k+d.b ∧ θ k+d.b≤d.b+B.delta :=
    ⟨(neg_le_neg ((min_le_right _ _).trans (min_le_right _ _))).trans (hθ k).1,(hθ k).2⟩
  let s := IsingBulk.Branch.radialParameter d.alpha ε
  let q := preferredSourceCoordinate τ B.p B.m s θ
  have hBa : AnalyticAt ℂ (fun z : ℂ × (Fin N → ℂ) => preferredResidualCollective z.1 z.2) (s,q) :=
    preferredResidualCollective_analyticAt_of_rescaled hN s q a (preferredAngularDiameter θ) ha hdiam
      ((hneigh N hN ε τ hε heA hτ htA θ hθA hdiam).1 0 (by simp))
  obtain ⟨hpoint,hθstrict⟩ := hframe δB hδB hδBB N hN ε τ hε heG hτ htG θ hθ
  obtain ⟨_,hMinv,hMj,hUj,hG⟩ := hFbound N hN ε τ hε heF hτ htF θ hθF
  have hMframe (b k : Fin N) (ys : List (Option (Fin N))) (hys : ys.length≤j) :
      ‖preferredFrameJet τ B.p B.m (fun _ x => (preferredContourMatrix τ B.p B.m x)⁻¹ b k) ys s θ‖≤
        CF^2*(N:ℝ)^(j*j+3*j) := by
    have hentry : ContDiff ℝ ∞ (fun x : Fin N → ℝ => (preferredContourMatrix τ B.p B.m x)⁻¹ b k) :=
      contDiff_pi.mp (contDiff_pi.mp hMinv b) k
    have hh := hG _ hentry (CF*(N:ℝ)^j) (by positivity) (hMj b k) ys hys
    apply hh.trans_eq
    rw [show j*j+3*j=(j*j+2*j)+j by omega,pow_add]
    ring
  have hdiamD : preferredAngularDiameter θ≤D := by
    apply Metric.diam_le_of_forall_dist_le (le_trans (by norm_num) hD)
    rintro _ ⟨b,rfl⟩ _ ⟨k,rfl⟩
    rw [Real.dist_eq]
    apply abs_le.mpr
    constructor <;> dsimp [D] <;> linarith [(hθ b).1,(hθ b).2,(hθ k).1,(hθ k).2]
  have hV := preferredAngularField_frame_bound_of_factors hN τ δ B.p B.m B.smooth B.m_smooth
    s θ hpoint hθstrict hBa j (j*j+3*j) (2*j+2) (CF^2) CF CB D (sq_nonneg _) hCFp.le hCB.le
    hdiam hdiamD hD hMframe (fun b ys hys => hUj ys hys b)
    (fun b ys hys => hBbound N hN ε τ hε heB hτ htB θ hθB hdiam ys hys b) xs hxs i
  have hBval := hBbound N hN ε τ hε heB hτ htB θ hθB hdiam xs hxs i
  have hn : (1:ℝ)≤N := by exact_mod_cast Nat.succ_le_iff.mpr hN
  have hBpow : (N:ℝ)^(2*j+2)≤(N:ℝ)^(j*j+5*j+3) :=
    pow_le_pow_right₀ hn (by omega)
  have hB' := hBval.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hBpow hCB.le) (by positivity))
  have hV' : ‖preferredFrameJet τ B.p B.m
      (fun t x => preferredSourceAngularField .right τ B.p B.m t x i) xs s θ‖≤
      CV*(N:ℝ)^(j*j+5*j+3)/preferredAngularDiameter θ^(1+preferredCoordinateJetOrder xs) := by
    convert hV using 1
    congr 2
    ring
  change ‖preferredFrameJet τ B.p B.m
    (fun t x => preferredResidualCollective t (preferredSourceCoordinate τ B.p B.m t x) i) xs s θ‖+
    ‖preferredFrameJet τ B.p B.m (fun t x => preferredSourceAngularField .right τ B.p B.m t x i) xs s θ‖≤_
  calc
    _ ≤ CB*(N:ℝ)^(j*j+5*j+3)/preferredAngularDiameter θ^(1+preferredCoordinateJetOrder xs)+
        CV*(N:ℝ)^(j*j+5*j+3)/preferredAngularDiameter θ^(1+preferredCoordinateJetOrder xs) :=
      add_le_add hB' hV'
    _ = _ := by ring

/-- The manuscript's named all-order B/V source obligation is proved. -/
theorem preferred_actual_global_collective_jet_bound (d : PreferredBranchData) :
    ∃ cap : ℝ, 0<cap ∧ cap<d.alpha ∧
      ∀ B : PreferredCoareaBump d, B.delta<cap →
      ∃ ε₀ τ₀ δB : ℝ, 0<ε₀ ∧ 0<τ₀ ∧ 0<δB ∧ δB<B.delta ∧
        ∀ τ : ℝ, 0≤τ → τ<τ₀ →
        PreferredGlobalCollectiveJetBound d τ B.p B.m B.delta δB ε₀ := by
  obtain ⟨cap,hcap,hcapa,hb⟩ := preferred_actual_collective_angular_frame_jets d
  refine ⟨cap,hcap,hcapa,?_⟩
  intro B hBcap
  obtain ⟨ε₀,τ₀,δB,hε₀,hτ₀,hδB,hδBB,hj⟩ := hb B hBcap
  refine ⟨ε₀,τ₀,δB,hε₀,hτ₀,hδB,hδBB,?_⟩
  intro τ hτ hτr j
  obtain ⟨C,hC,hbound⟩ := hj j
  refine ⟨C,j*j+5*j+3,hC,?_⟩
  intro N hN ε θ hε hεr hθ hdiam xs hxs i
  exact hbound N (by omega) ε τ hε hεr hτ hτr θ
    (fun k => ⟨by have := (hθ k).1; linarith,by have := (hθ k).2; linarith⟩)
    hdiam xs hxs i

end
end IsingBulk.Preferred22
