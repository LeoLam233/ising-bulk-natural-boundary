import IsingBulk.Preferred22.SourceCollectiveDifference
import IsingBulk.Preferred22.AnisotropicCauchy
import IsingBulk.Preferred22.FrameDomain
import IsingBulk.Preferred22.SourceFrameGeometry

/-! All fixed mixed complex parameter/q and true source-frame jets of the actual pair-diagonal factor.
The derivative-order constant is chosen before N, epsilon and configuration.
The exact physical frame pullback is included below. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set Metric
open scoped ContDiff BigOperators Topology
set_option backward.isDefEq.respectTransparency false

/-- Actual all-order anisotropic collective jet bound. A pure parameter
direction has weight one; a pure q direction has weight 1/diameter. Thus
every q derivative costs one diameter, while parameter jets cost none. -/
theorem preferred_actual_collective_difference_mixed_jets (d : PreferredBranchData) :
    ∃ cap : ℝ, 0<cap ∧ cap<d.alpha ∧
      ∀ B : PreferredCoareaBump d, B.delta<cap →
      ∃ ε₀ τ₀ δB : ℝ, 0<ε₀ ∧ 0<τ₀ ∧ 0<δB ∧ δB<B.delta ∧
        ∀ n : ℕ, ∃ C : ℝ, 0<C ∧
        ∀ N : ℕ, 0<N → ∀ ε τ : ℝ, 0<ε → ε<ε₀ → 0≤τ → τ<τ₀ →
        ∀ θ : Fin N → ℝ,
        (∀ i, -δB≤θ i+d.b ∧ θ i+d.b≤d.b+B.delta) →
        0<preferredAngularDiameter θ →
        ∀ i j : Fin N, ∀ v : Fin n → ℂ × (Fin N → ℂ),
        let s := IsingBulk.Branch.radialParameter d.alpha ε
        let q := preferredSourceCoordinate τ B.p B.m s θ
        ‖iteratedFDeriv ℂ n
          (fun z : ℂ × (Fin N → ℂ) => preferredCollectiveDifferenceFactor z.1 z.2 i j) (s,q) v‖≤
          C*(N:ℝ)^(2*n+2)/(preferredAngularDiameter θ)^2 *
            ∏ k, max ‖(v k).1‖ (‖(v k).2‖/preferredAngularDiameter θ) := by
  obtain ⟨cap,hcap,hcapa,hfield⟩ := preferred_actual_collective_difference_neighborhood d
  refine ⟨cap,hcap,hcapa,?_⟩
  intro B hBcap
  obtain ⟨η,M,ε₀,τ₀,δB,hη,hM,hε₀,hτ₀,hδB,hδBB,hlocal⟩ := hfield B hBcap
  refine ⟨ε₀,τ₀,δB,hε₀,hτ₀,hδB,hδBB,?_⟩
  intro n
  let C := cauchyJetConstant n*M/η^n
  have hC : 0<C := div_pos (mul_pos (cauchyJetConstant_pos n) hM) (pow_pos hη n)
  refine ⟨C,hC,?_⟩
  intro N hN ε τ hε hεr hτ hτr θ hθ hdiam i j v
  dsimp only
  let s := IsingBulk.Branch.radialParameter d.alpha ε
  let q := preferredSourceCoordinate τ B.p B.m s θ
  let diam := preferredAngularDiameter θ
  let a := η/(N:ℝ)^2
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have ha : 0<a := div_pos hη (sq_pos_of_pos hn)
  obtain ⟨hf,hb⟩ := hlocal N hN ε τ hε hεr hτ hτr θ hθ hdiam i j
  have haeq : a*diam=η*diam/(N:ℝ)^2 := by dsimp [a]; ring
  let F : ℂ × (Fin N → ℂ) → ℂ := fun z => preferredCollectiveDifferenceFactor z.1 z.2 i j
  have hf' : AnalyticOnNhd ℂ (fun z : ℂ × (Fin N → ℂ) =>
      F (s+(a:ℂ)*z.1,q+((a*diam:ℝ):ℂ) • z.2)) (ball 0 1) := by
    rw [haeq]
    exact hf
  have hb' : ∀ z∈ball (0 : ℂ × (Fin N → ℂ)) 1,
      ‖F (s+(a:ℂ)*z.1,q+((a*diam:ℝ):ℂ) • z.2)‖≤M*(N:ℝ)^2/diam^2 := by
    rw [haeq]
    exact hb
  have hh := anisotropic_cauchy_mixed_bound F (s,q) a diam (M*(N:ℝ)^2/diam^2)
    ha hdiam hf' hb' n v
  have hpow : (N:ℝ)^(2*n+2)=(N:ℝ)^2*((N:ℝ)^2)^n := by
    rw [pow_add,pow_mul]
    ring
  convert hh using 1
  rw [hpow]
  dsimp only [C,a]
  rw [div_pow]
  field_simp [hη.ne',hn.ne',hdiam.ne',diam]
  dsimp only [diam]
  ring


theorem preferredCollectiveDifferenceFactor_analyticAt_of_rescaled {N : ℕ} (hN : 0<N)
    (s : ℂ) (q : Fin N → ℂ) (i j : Fin N) (η d : ℝ) (hη : 0<η) (hd : 0<d)
    (hf : AnalyticAt ℂ (preferredRescaledCollectiveDifference s q η d i j) 0) :
    AnalyticAt ℂ (fun z : ℂ × (Fin N → ℂ) => preferredCollectiveDifferenceFactor z.1 z.2 i j) (s,q) := by
  let a := η/(N:ℝ)^2
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have ha : 0<a := div_pos hη (sq_pos_of_pos hn)
  have haC : (a:ℂ)≠0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hadC : ((a*d:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr (mul_pos ha hd).ne'
  let L := complexAnisotropicScale (E:=Fin N → ℂ) (a:ℂ) ((a*d:ℝ):ℂ) haC hadC
  let F : ℂ × (Fin N → ℂ) → ℂ := fun z => preferredCollectiveDifferenceFactor z.1 z.2 i j
  have he : a*d=η*d/(N:ℝ)^2 := by dsimp [a]; ring
  have hH : AnalyticAt ℂ (fun z => F ((s,q)+L z)) 0 := by
    change AnalyticAt ℂ (fun z : ℂ × (Fin N → ℂ) =>
      F (s+(a:ℂ)*z.1,q+((a*d:ℝ):ℂ) • z.2)) 0
    rw [he]
    exact hf
  have hlin : AnalyticAt ℂ (fun z : ℂ × (Fin N → ℂ) => L.symm (z-(s,q))) (s,q) :=
    (L.symm.analyticAt _).comp (analyticAt_id.sub analyticAt_const)
  have hh := hH.comp_of_eq hlin (by simp)
  apply hh.congr
  exact Filter.Eventually.of_forall (fun z => by simp only [Function.comp_def,
    ContinuousLinearEquiv.apply_symm_apply,add_sub_cancel]; rfl)


/-- True all-order frame jets of Cij. The factor itself costs two
configuration diameters, and each coordinate letter costs one more.
The exact pair identity remains valid at every partial collision. -/
theorem preferred_actual_collective_difference_frame_jets (d : PreferredBranchData) :
    ∃ cap : ℝ, 0<cap ∧ cap<d.alpha ∧
      ∀ B : PreferredCoareaBump d, B.delta<cap →
      ∃ ε₀ τ₀ δB : ℝ, 0<ε₀ ∧ 0<τ₀ ∧ 0<δB ∧ δB<B.delta ∧
        ∀ j : ℕ, ∃ C : ℝ, 0<C ∧
        ∀ N : ℕ, 0<N → ∀ ε τ : ℝ, 0<ε → ε<ε₀ → 0≤τ → τ<τ₀ →
        ∀ θ : Fin N → ℝ,
        (∀ i, -δB≤θ i+d.b ∧ θ i+d.b≤d.b+B.delta) →
        0<preferredAngularDiameter θ →
        ∀ xs : List (Option (Fin N)), xs.length≤j → ∀ a b : Fin N,
        ‖preferredFrameJet τ B.p B.m
          (fun s x => preferredCollectiveDifferenceFactor s (preferredSourceCoordinate τ B.p B.m s x) a b)
          xs (IsingBulk.Branch.radialParameter d.alpha ε) θ‖≤
          C*(N:ℝ)^(2*j+2)/preferredAngularDiameter θ^(2+preferredCoordinateJetOrder xs) := by
  obtain ⟨cap₁,hcap₁,hcap₁a,hjets⟩ := preferred_actual_collective_difference_mixed_jets d
  obtain ⟨cap₂,hcap₂,hcap₂a,hlocal⟩ := preferred_actual_collective_difference_neighborhood d
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
  intro N hN ε τ hε hεr hτ hτr θ hθ hdiam xs hxs a b
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
  let F : ℂ × (Fin N → ℂ) → ℂ := fun z => preferredCollectiveDifferenceFactor z.1 z.2 a b
  have hF : AnalyticAt ℂ F (s,q) :=
    preferredCollectiveDifferenceFactor_analyticAt_of_rescaled hN s q a b η (preferredAngularDiameter θ) hη hdiam
      ((hneigh N hN ε τ hε hεr₂ hτ hτr₂ θ hθ₂ hdiam a b).1 0 (by simp))
  obtain ⟨hpoint,hθstrict⟩ := hframe δB hδB hδBB N hN ε τ hε hεr₃ hτ hτr₃ θ hθ
  have hpull := preferredFrameJet_pullback τ δ B.p B.m B.smooth B.m_smooth s θ
    hpoint hθstrict F hF xs
  change ‖preferredFrameJet τ B.p B.m (fun t x => F (t,preferredSourceCoordinate τ B.p B.m t x)) xs s θ‖≤_
  rw [hpull,preferredComplexFrameJet_eq_iteratedFDeriv F xs (s,q) hF]
  have hbound := hCjet xs.length N hN ε τ hε hεr₁ hτ hτr₁ θ hθ₁ hdiam a b
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
    _ ≤ C xs.length*(N:ℝ)^(2*xs.length+2)/(preferredAngularDiameter θ)^2 *
        (1/preferredAngularDiameter θ^preferredCoordinateJetOrder xs) := hbound
    _ ≤ Cj*(N:ℝ)^(2*j+2)/(preferredAngularDiameter θ)^2 *
        (1/preferredAngularDiameter θ^preferredCoordinateJetOrder xs) := by
      exact mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (mul_le_mul hCk hpow (by positivity) hCj.le) (sq_nonneg _))
        (by positivity)
    _ = _ := by rw [pow_add (preferredAngularDiameter θ) 2 _]; ring


end
end IsingBulk.Preferred22
