import IsingBulk.Preferred22.FrameDomain
import IsingBulk.Preferred22.SourceFrameGeometry
import IsingBulk.Preferred22.CollectiveAnalyticSource

/-! Literal all-order source-frame derivatives of the genuine collective
field. The source neighborhood and every inverse/curvature/occupancy margin
are discharged before choosing particle number or derivative order. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set Metric
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false

/-- The B part of manuscript (7.14), for arbitrary mixed words in the
actual E_s and E_a frames. Only coordinate letters cost a diameter. This
statement concerns the true B pullback; the angular vector V has a separate
matrix/frame estimate and is not silently included here. -/
theorem preferred_actual_collective_frame_jets (d : PreferredBranchData) :
    ∃ cap : ℝ, 0<cap ∧ cap<d.alpha ∧
      ∀ B : PreferredCoareaBump d, B.delta<cap →
      ∃ ε₀ τ₀ δB : ℝ, 0<ε₀ ∧ 0<τ₀ ∧ 0<δB ∧ δB<B.delta ∧
        ∀ j : ℕ, ∃ C : ℝ, 0<C ∧
        ∀ N : ℕ, 0<N → ∀ ε τ : ℝ, 0<ε → ε<ε₀ → 0≤τ → τ<τ₀ →
        ∀ θ : Fin N → ℝ,
        (∀ i, -δB≤θ i+d.b ∧ θ i+d.b≤d.b+B.delta) →
        0<preferredAngularDiameter θ →
        ∀ xs : List (Option (Fin N)), xs.length≤j → ∀ i : Fin N,
        ‖preferredFrameJet τ B.p B.m
          (fun s x => preferredResidualCollective s (preferredSourceCoordinate τ B.p B.m s x) i)
          xs (IsingBulk.Branch.radialParameter d.alpha ε) θ‖≤
          C*(N:ℝ)^(2*j+2)/preferredAngularDiameter θ^(1+preferredCoordinateJetOrder xs) := by
  obtain ⟨cap₁,hcap₁,hcap₁a,hjets⟩ := preferred_actual_collective_mixed_jets d
  obtain ⟨cap₂,hcap₂,hcap₂a,hlocal⟩ := preferred_actual_collective_neighborhood d
  refine ⟨min cap₁ cap₂,lt_min hcap₁ hcap₂,(min_le_left _ _).trans_lt hcap₁a,?_⟩
  intro B hBcap
  obtain ⟨ε₁,τ₁,δ₁,hε₁,hτ₁,hδ₁,hδ₁B,hjet⟩ := hjets B (hBcap.trans_le (min_le_left _ _))
  obtain ⟨η,M,ε₂,τ₂,δ₂,hη,hM,hε₂,hτ₂,hδ₂,hδ₂B,hneigh⟩ :=
    hlocal B (hBcap.trans_le (min_le_right _ _))
  obtain ⟨δ,ε₃,τ₃,hδ,hδa,hε₃,hτ₃,hframe⟩ := preferred_actual_frame_points d B
  let ε₀ := min ε₁ (min ε₂ ε₃)
  let τ₀ := min τ₁ (min τ₂ τ₃)
  let δB := min δ₁ δ₂
  have hδB : 0<δB := lt_min hδ₁ hδ₂
  have hδBB : δB<B.delta := (min_le_left _ _).trans_lt hδ₁B
  refine ⟨ε₀,τ₀,δB,lt_min hε₁ (lt_min hε₂ hε₃),
    lt_min hτ₁ (lt_min hτ₂ hτ₃),hδB,hδBB,?_⟩
  choose C hC hCjet using hjet
  intro j
  let Cj := 1+∑ k∈Finset.range (j+1), C k
  have hsum : 0≤∑ k∈Finset.range (j+1), C k :=
    Finset.sum_nonneg (fun k _ => (hC k).le)
  have hCj : 0<Cj := by dsimp [Cj]; linarith
  refine ⟨Cj,hCj,?_⟩
  intro N hN ε τ hε hεr hτ hτr θ hθ hdiam xs hxs i
  have hεr₁ : ε<ε₁ := hεr.trans_le (min_le_left _ _)
  have hεr₂ : ε<ε₂ := hεr.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hεr₃ : ε<ε₃ := hεr.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hτr₁ : τ<τ₁ := hτr.trans_le (min_le_left _ _)
  have hτr₂ : τ<τ₂ := hτr.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hτr₃ : τ<τ₃ := hτr.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hθ₁ (a : Fin N) : -δ₁≤θ a+d.b ∧ θ a+d.b≤d.b+B.delta :=
    ⟨(neg_le_neg (min_le_left _ _)).trans (hθ a).1,(hθ a).2⟩
  have hθ₂ (a : Fin N) : -δ₂≤θ a+d.b ∧ θ a+d.b≤d.b+B.delta :=
    ⟨(neg_le_neg (min_le_right _ _)).trans (hθ a).1,(hθ a).2⟩
  let s := IsingBulk.Branch.radialParameter d.alpha ε
  let q := preferredSourceCoordinate τ B.p B.m s θ
  let F : ℂ × (Fin N → ℂ) → (Fin N → ℂ) := fun z => preferredResidualCollective z.1 z.2
  have hF : AnalyticAt ℂ F (s,q) :=
    preferredResidualCollective_analyticAt_of_rescaled hN s q η (preferredAngularDiameter θ) hη hdiam
      ((hneigh N hN ε τ hε hεr₂ hτ hτr₂ θ hθ₂ hdiam).1 0 (by simp))
  obtain ⟨hpoint,hθstrict⟩ := hframe δB hδB hδBB N hN ε τ hε hεr₃ hτ hτr₃ θ hθ
  have hpull := preferredFrameJet_pullback τ δ B.p B.m B.smooth B.m_smooth s θ
    hpoint hθstrict (fun z => F z i) ((analyticAt_pi_iff.mp hF) i) xs
  change ‖preferredFrameJet τ B.p B.m (fun t x => F (t,preferredSourceCoordinate τ B.p B.m t x) i) xs s θ‖≤_
  rw [hpull,preferredComplexFrameJet_apply F xs (s,q) hF i,
    preferredComplexFrameJet_eq_iteratedFDeriv F xs (s,q) hF]
  have hbound := hCjet xs.length N hN ε τ hε hεr₁ hτ hτr₁ θ hθ₁ hdiam
    (preferredFrameDirections xs)
  rw [preferredFrameDirections_weight_product xs (preferredAngularDiameter θ) hdiam] at hbound
  have hCk : C xs.length≤Cj := by
    have hh := Finset.single_le_sum (fun k (_ : k∈Finset.range (j+1)) => (hC k).le)
      (show xs.length∈Finset.range (j+1) by simp; omega)
    dsimp only [Cj]
    linarith
  have hN1 : (1:ℝ)≤N := by exact_mod_cast Nat.succ_le_iff.mpr hN
  have hpow : (N:ℝ)^(2*xs.length+2)≤(N:ℝ)^(2*j+2) :=
    pow_le_pow_right₀ hN1 (by omega)
  calc
    _ ≤ ‖iteratedFDeriv ℂ xs.length F (s,q) (preferredFrameDirections xs)‖ := norm_le_pi_norm _ i
    _ ≤ C xs.length*(N:ℝ)^(2*xs.length+2)/preferredAngularDiameter θ *
        (1/preferredAngularDiameter θ^preferredCoordinateJetOrder xs) := hbound
    _ ≤ Cj*(N:ℝ)^(2*j+2)/preferredAngularDiameter θ *
        (1/preferredAngularDiameter θ^preferredCoordinateJetOrder xs) := by
      exact mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (mul_le_mul hCk hpow (by positivity) hCj.le) hdiam.le)
        (by positivity)
    _ = _ := by rw [pow_add (preferredAngularDiameter θ) 1 _,pow_one]; ring

end
end IsingBulk.Preferred22
