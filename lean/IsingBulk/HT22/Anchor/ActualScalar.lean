import IsingBulk.HT22.Anchor.SeedFrames
import IsingBulk.HT22.Anchor.MovingFrameJets
namespace IsingBulk.HT22.Anchor
noncomputable section
open Set Filter IsingBulk.Preferred22
open scoped Topology ContDiff BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- All actual odd anchored descendants satisfy a factorial-decaying scalar
bound times the unchanged Jacobian. The field is the F001 fixed-v anchor;
its moving-frame correction is included, and the complete signed resolvent
is differentiated inside the scalar, never assumed frozen. -/
theorem actual_anchor_scalar_bound (d : PreferredBranchData) :
    ∃ cap : ℝ,0<cap ∧ cap<d.alpha ∧
      ∀ B : PreferredCoareaBump d,B.delta<cap → ∀ δB : ℝ,0<δB →
      ∃ ε₀ τ₀ : ℝ,0<ε₀ ∧ 0<τ₀ ∧
      ∀ rcut : ℝ → ℝ,ContDiff ℝ ∞ rcut → Function.Periodic rcut (2*Real.pi) →
      ∀ J : ℕ,∃ C : ℝ,1≤C ∧
      ∀ N : ℕ,0<N → ∀ σ : ℂ,‖σ‖=1 → ∀ ε τ : ℝ,0<ε → ε<ε₀ → 0≤τ → τ<τ₀ →
      ∀ θ : Fin N → ℝ,(∀ i,θ i∈Icc (-Real.pi-B.delta) B.delta) →
      ∀ a : Fin N,θ a≤ -d.b-δB/2 → ∀ j≤J,
      let s := IsingBulk.Branch.radialParameter d.alpha ε
      ‖transportedDensity a σ τ preferredPopulationCutoff B.p B.m rcut j s θ‖≤
        ‖Tail.coordinateJacobian τ B.p B.m s θ‖*((C/Real.sqrt N)^N*(N:ℝ)^(J*J+8*J+1)) := by
  obtain ⟨capF,hcapF,hcapFa,hfield⟩ := actual_moving_anchor_frame_jets d
  obtain ⟨capW,hcapW,_hcapWa,hweight⟩ := preferred_actual_anchor_cell_weight_frame_jets d
  obtain ⟨capA,hcapA,_hcapAa,hamplitude⟩ := actual_amplitude_jets d
  let cap := min capF (min capW capA)
  refine ⟨cap,lt_min hcapF (lt_min hcapW hcapA),(min_le_left _ _).trans_lt hcapFa,?_⟩
  intro B hB δB hδB
  obtain ⟨εf,τf,hεf,hτf,hfield'⟩ := hfield B (hB.trans_le (min_le_left _ _)) δB hδB
  obtain ⟨εw,τw,hεw,hτw,hweight'⟩ := hweight B
    (hB.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  obtain ⟨εa,τa,hεa,hτa,hamplitude'⟩ := hamplitude B
    (hB.trans_le ((min_le_right _ _).trans (min_le_right _ _))) δB hδB
  obtain ⟨δ,εg,τg,_hδ,_hδa,hεg,hτg,hframe⟩ := preferred_actual_whole_frame_points d B
  let ε₀ := min εf (min εw (min εa εg))
  let τ₀ := min τf (min τw (min τa τg))
  refine ⟨ε₀,τ₀,lt_min hεf (lt_min hεw (lt_min hεa hεg)),
    lt_min hτf (lt_min hτw (lt_min hτa hτg)),?_⟩
  intro rcut hrcut hrper J
  obtain ⟨F,hF,hFjet⟩ := hfield' J
  obtain ⟨W,hW,hWjet⟩ := hweight' rcut hrcut hrper J
  obtain ⟨A,hA,hAjet⟩ := hamplitude' J
  let D := 1+2^(J+1)*F
  have hD : 1≤D := by
    have : 0≤2^(J+1)*F := by positivity
    dsimp [D]
    linarith
  let S := 2^J*D^J
  have hS : 1≤S := one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (one_le_pow₀ hD)
  let C := S*W*A
  have hC : 1≤C := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hS hW) hA
  refine ⟨C,hC,?_⟩
  intro N hN σ hσ ε τ hε hεr hτ hτr θ hθ a ha j hj
  dsimp only
  let s := IsingBulk.Branch.radialParameter d.alpha ε
  have hN1 : (1:ℝ)≤N := by exact_mod_cast hN
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  have heF : ε<εf := hεr.trans_le (min_le_left _ _)
  have heW : ε<εw := hεr.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have heA : ε<εa := hεr.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have heG : ε<εg := hεr.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have htF : τ<τf := hτr.trans_le (min_le_left _ _)
  have htW : τ<τw := hτr.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have htA : τ<τa := hτr.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have htG : τ<τg := hτr.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨hpoint,hstrict⟩ := hframe N hN ε τ hε heG hτ htG θ hθ
  obtain ⟨hAa,hAj⟩ := hAjet N hN σ hσ ε τ hε heA hτ htA θ hθ a ha
  have hFsource (i : Fin N) (ys : List (Option (Fin N))) (hys : ys.length≤J) :
      ‖preferredFrameJet τ B.p B.m
        (fun t x => movingSourceResidual a τ B.p B.m t x i) ys s θ‖≤F*(N:ℝ) :=
    hFjet N hN ε τ hε heF hτ htF θ hθ a ha ys hys i
  have hWsource (ys : List (Option (Fin N))) (hys : ys.length≤J) :
      ‖preferredFrameJet τ B.p B.m
        (fun _ x => (preferredCellWeight (.anchor a) preferredPopulationCutoff B.p B.m rcut x:ℂ)) ys s θ‖≤
        W^N*(N:ℝ)^(J*J+5*J) := hWjet N hN ε τ hε heW hτ htW θ hθ a ys hys
  have hAsource (ys : List (Option (Fin N))) (hys : ys.length≤J) :
      ‖preferredFrameJet τ B.p B.m
        (fun t x => amplitude σ t (preferredSourceCoordinate τ B.p B.m t x)) ys s θ‖≤
        (A/Real.sqrt N)^N*(N:ℝ)^(J+1) := by
    exact preferred_frame_analytic_projection_bound τ δ B.p B.m B.smooth B.m_smooth s θ hpoint hstrict
      (fun z : ℂ × (Fin N → ℂ) => amplitude σ z.1 z.2)
      (fun z : ℂ × (Fin N → ℂ) => amplitude σ z.1 z.2)
      (ContinuousLinearMap.id ℂ (ℂ × (Fin N → ℂ))) (fun _ => le_rfl) hAa Filter.EventuallyEq.rfl ys
      ((A/Real.sqrt N)^N*(N:ℝ)^(J+1)) (by have := zero_le_one.trans hA; positivity) (hAj ys.length hys)
  have hscalar := scalar_bound_at hN a σ hσ.le τ δ preferredPopulationCutoff B.p B.m rcut
    preferredPopulationCutoff_smooth B.smooth B.m_smooth hrcut s θ hpoint hstrict hAa J
    (F*(N:ℝ)) (W^N*(N:ℝ)^(J*J+5*J)) ((A/Real.sqrt N)^N*(N:ℝ)^(J+1))
    (by positivity) (by have := zero_le_one.trans hW; positivity)
    (by have := zero_le_one.trans hA; positivity) hFsource hWsource hAsource j hj
  have hbase : 1+2^(J+1)*(N:ℝ)*(F*(N:ℝ))≤D*(N:ℝ)^2 := by
    have hn2 : 1≤(N:ℝ)^2 := one_le_pow₀ hN1
    dsimp [D]
    nlinarith
  have hpow : (1+2^(J+1)*(N:ℝ)*(F*(N:ℝ)))^j≤D^J*(N:ℝ)^(2*J) := by
    calc
      _ ≤ (D*(N:ℝ)^2)^j := pow_le_pow_left₀ (by positivity) hbase j
      _ = D^j*(N:ℝ)^(2*j) := by rw [mul_pow,pow_mul]
      _ ≤ _ := mul_le_mul (pow_le_pow_right₀ hD hj) (pow_le_pow_right₀ hN1 (by omega))
        (by positivity) (by have := zero_le_one.trans hD; positivity)
  have hbound : ‖regularTransportedScalar a σ τ preferredPopulationCutoff B.p B.m rcut j s θ‖≤
      (C/Real.sqrt N)^N*(N:ℝ)^(J*J+8*J+1) := by
    apply hscalar.trans
    calc
      _ ≤ (D^J*(N:ℝ)^(2*J))*(2^J*(W^N*(N:ℝ)^(J*J+5*J))*((A/Real.sqrt N)^N*(N:ℝ)^(J+1))) :=
        mul_le_mul_of_nonneg_right hpow (by have := zero_le_one.trans hW; have := zero_le_one.trans hA; positivity)
      _ = S*W^N*(A/Real.sqrt N)^N*(N:ℝ)^(J*J+8*J+1) := by
        dsimp [S]
        rw [show J*J+8*J+1=2*J+(J*J+5*J)+(J+1) by omega,pow_add,pow_add]
        ring
      _ ≤ S^N*W^N*(A/Real.sqrt N)^N*(N:ℝ)^(J*J+8*J+1) := by
        gcongr
        exact le_self_pow₀ hS (by omega)
      _ = _ := by
        dsimp [C,S]
        simp only [mul_pow,div_pow]
        ring
  obtain ⟨Ω,hΩ,hz,hΩpoint,_hΩstrict⟩ := preferred_strict_frame_chart τ δ B.p B.m
    B.smooth B.m_smooth s θ hpoint hstrict
  rw [transportedDensity_eq_reconstructed hN a σ hσ.le τ δ preferredPopulationCutoff B.p B.m rcut
    preferredPopulationCutoff_smooth B.smooth B.m_smooth hrcut Ω hΩ hΩpoint j s θ hz,norm_mul]
  exact mul_le_mul_of_nonneg_left hbound (norm_nonneg _)

end
end IsingBulk.HT22.Anchor
