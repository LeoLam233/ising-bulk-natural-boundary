import IsingBulk.Tail.CompactRightPhaseJets
import IsingBulk.Tail.CompactAnalyticJetBounds
import IsingBulk.Tail.DeformedRadialTransfer

/-! Uniform scalar phase jets attached to actual coupled radial points.
The jet dimension is fixed (three complex scalars); the actual N-dependent
occupancy remains in the inner real deformation map. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set Metric
open scoped Topology

 theorem compactPhaseModel_compact_tube {S a b : ℝ}
    (hmargin : ∀ θ ∈ Icc a b, |S-Real.cos θ|<1) (k : ℕ) :
    ∃ r B : ℝ, 0<r ∧ 0<B ∧ ∀ θ ∈ Icc a b, ∀ S' v : ℂ,
      max ‖S'-(S:ℂ)‖ ‖v‖≤r → ∀ j≤k,
      ‖iteratedFDeriv ℂ j compactPhaseModel (S',v,(θ:ℂ))‖≤B ∧
      ‖iteratedFDeriv ℂ j compactPhaseModel (S',v,(θ:ℂ))-
        iteratedFDeriv ℂ j compactPhaseModel ((S:ℂ),0,(θ:ℂ))‖≤B*max ‖S'-(S:ℂ)‖ ‖v‖ := by
  let K := (fun θ : ℝ => ((S:ℂ),(0:ℂ),(θ:ℂ))) '' Icc a b
  have hK : IsCompact K := isCompact_Icc.image (by fun_prop)
  have hf : AnalyticOnNhd ℂ compactPhaseModel K := by
    rintro x ⟨θ,hθ,rfl⟩
    exact compactPhaseModel_analyticAt S θ (hmargin θ hθ)
  obtain ⟨r,B,hr,hB,hjets⟩ := compact_analytic_jet_bounds compactPhaseModel hK hf k
  refine ⟨r,B,hr,hB,?_⟩
  intro θ hθ S' v hv j hj
  have hn : ‖(S',v,(θ:ℂ))-((S:ℂ),0,(θ:ℂ))‖=max ‖S'-(S:ℂ)‖ ‖v‖ := by
    simp [Prod.norm_def]
  have hh := hjets ((S:ℂ),0,(θ:ℂ)) ⟨θ,hθ,rfl⟩ (S',v,(θ:ℂ)) (by rwa [hn]) j hj
  simpa only [hn] using hh

 theorem compactPhaseModel_source_identity {N : ℕ} (f : SelectorFunctions)
    (c₀ eps τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ) (i : Fin N) :
    continuedPhase (sourceW s (deformedPoint f (Real.exp (-c₀*eps)) τ lam θ i))=
      compactPhaseModel (sourceS s,
        (coupledRadialExponent c₀ eps τ lam (f.p (θ i)) (f.m (θ i))
          (occupancy (fun j => f.p (θ j))/(N:ℝ)):ℂ),(θ i:ℂ)) := by
  rw [deformedPoint_coupledRadialExponent]
  unfold compactPhaseModel
  congr 1
  exact polar_dispersion _ _ _

 theorem coupledRadialExponent_lambda_bound {c₀ eps τ lam p m ρ : ℝ}
    (hc : 0≤c₀) (heps : 0≤eps) (hτ : 0≤τ) (hl : 0≤lam)
    (hp0 : 0≤p) (hp1 : p≤1) (hm0 : 0≤m) (hm1 : m≤1) (hρ0 : 0≤ρ) (hρ1 : ρ≤1) :
    |coupledRadialExponent c₀ eps τ lam p m ρ|≤c₀*eps+2*τ*lam := by
  have hh := coupledRadialExponent_bound hc heps (mul_nonneg hl hτ) (by norm_num : (0:ℝ)≤1)
    le_rfl hp0 hp1 hm0 hm1 hρ0 hρ1
  have he : coupledRadialExponent c₀ eps (lam*τ) 1 p m ρ=coupledRadialExponent c₀ eps τ lam p m ρ := by
    unfold coupledRadialExponent
    ring
  rw [he] at hh
  nlinarith

 theorem compactPhaseModel_actual_radial_jets (d : LocalBranchData) {a b : ℝ}
    (hmargin : ∀ θ ∈ Icc a b, |1+Real.cos d.thetaB-Real.cos θ|<1) (k : ℕ) :
    ∃ r B : ℝ, 0<r ∧ 0<B ∧ ∀ (N : ℕ) (f : SelectorFunctions) (eps τ lam : ℝ)
      (θ : Fin N → ℝ) (i : Fin N),
      0<N → 0≤eps → 0≤τ → 0≤lam →
      (∀ x, 0≤f.p x ∧ f.p x≤1) → (∀ x, 0≤f.m x ∧ f.m x≤1) →
      θ i ∈ Icc a b → (3+d.c₀)*eps+2*τ*lam≤r →
      let v := (coupledRadialExponent d.c₀ eps τ lam (f.p (θ i)) (f.m (θ i))
        (occupancy (fun l => f.p (θ l))/(N:ℝ)):ℂ)
      ∀ j≤k,
        ‖iteratedFDeriv ℂ j compactPhaseModel (sourceS (radialParameter d.theta eps),v,(θ i:ℂ))‖≤B ∧
        ‖iteratedFDeriv ℂ j compactPhaseModel (sourceS (radialParameter d.theta eps),v,(θ i:ℂ))-
          iteratedFDeriv ℂ j compactPhaseModel (((1+Real.cos d.thetaB:ℝ):ℂ),0,(θ i:ℂ))‖≤
            B*((3+d.c₀)*eps+2*τ*lam) := by
  obtain ⟨r,B,hr,hB,hjets⟩ := compactPhaseModel_compact_tube hmargin k
  refine ⟨r,B,hr,hB,?_⟩
  intro N f eps τ lam θ i hN heps hτ hl hp hm hθ hsmall
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have hP0 := occupancy_nonneg (fun i => (hp (θ i)).1)
  have hP1 := occupancy_le (fun i => (hp (θ i)).2)
  have hv := coupledRadialExponent_lambda_bound d.c₀_pos.le heps hτ hl (hp (θ i)).1 (hp (θ i)).2 (hm (θ i)).1 (hm (θ i)).2
    (div_nonneg hP0 hn.le) ((div_le_one hn).mpr hP1)
  have hs := sourceS_radial_to_boundary d eps heps
  have hmax : max ‖sourceS (radialParameter d.theta eps)-((1+Real.cos d.thetaB:ℝ):ℂ)‖
      ‖(coupledRadialExponent d.c₀ eps τ lam (f.p (θ i)) (f.m (θ i))
        (occupancy (fun l => f.p (θ l))/(N:ℝ)):ℂ)‖ ≤ (3+d.c₀)*eps+2*τ*lam := by
    rw [max_le_iff,Complex.norm_real,Real.norm_eq_abs]
    constructor <;> nlinarith [mul_nonneg d.c₀_pos.le heps,mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) hτ) hl]
  dsimp only
  intro j hj
  have hh := hjets (θ i) hθ _ _ (hmax.trans hsmall) j hj
  exact ⟨hh.1,hh.2.trans (mul_le_mul_of_nonneg_left hmax hB.le)⟩

end
end IsingBulk.Tail
