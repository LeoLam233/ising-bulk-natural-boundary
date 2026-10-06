import IsingBulk.Tail.MixedSectorAsymptotic
import IsingBulk.Tail.LeftCompactSectorAsymptotic

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set Filter Asymptotics
open scoped Topology

def radialSeriesSmall (E : ℝ → ℕ → ℝ) : Prop :=
  (∀ᶠ eps : ℝ in 𝓝[>] 0,Summable (E eps)) ∧
    (fun eps : ℝ => ∑' N,E eps N) =o[𝓝[>] 0] (fun eps : ℝ => (Real.sqrt eps)⁻¹)

theorem radialSeriesSmall.add {E F : ℝ → ℕ → ℝ} (hE : radialSeriesSmall E) (hF : radialSeriesSmall F) :
    radialSeriesSmall (fun eps N => E eps N+F eps N) := by
  refine ⟨?_,?_⟩
  · filter_upwards [hE.1,hF.1] with eps he hf
    exact he.add hf
  · apply (hE.2.add hF.2).congr'
    · filter_upwards [hE.1,hF.1] with eps he hf
      exact (he.tsum_add hf).symm
    · exact Eventually.of_forall (fun _ => rfl)

def mixedLeftSectorNorm (N : ℕ) (f : SelectorFunctions) (r τ b outer inner : ℝ)
    (ho : 0<outer) (hi : 0< inner) (k : ℕ) (s : ℂ) (cut : ℝ) : ℝ :=
  originalMixedSectorNorm N f r τ b outer inner ho hi k s+
  originalLeftCompactSectorNorm N f r τ b outer inner ho hi k s+
  integratedMixedSectorNorm N f r τ b outer inner ho hi k s cut+
  integratedLeftCompactSectorNorm N f r τ b outer inner ho hi k s cut

theorem sector_assignment_mixed_left_right_cases {N : ℕ} (sigma : Fin N → Fin 3) :
    (∃ j,sigma j=2) ∨ leftCompactAssignment sigma ∨ (∀ i,sigma i=1) := by
  classical
  by_cases hb : ∃ j,sigma j=2
  · exact Or.inl hb
  have hn (i : Fin N) : sigma i≠2 := fun hi => hb ⟨i,hi⟩
  by_cases hl : ∃ i,sigma i=0
  · exact Or.inr (Or.inl ⟨hn,hl⟩)
  refine Or.inr (Or.inr ?_)
  intro i
  have hn0 : sigma i≠0 := fun hi => hl ⟨i,hi⟩
  have hn2 := hn i
  generalize hc : sigma i=c at hn0 hn2 ⊢
  fin_cases c <;> simp_all

theorem mixedLeftSectorNorm_nonneg (N : ℕ) (f : SelectorFunctions) (r τ b outer inner : ℝ)
    (ho : 0<outer) (hi : 0< inner) (k : ℕ) (s : ℂ) (cut : ℝ) :
    0≤mixedLeftSectorNorm N f r τ b outer inner ho hi k s cut :=
  add_nonneg (add_nonneg (add_nonneg (originalMixedSectorNorm_nonneg N f r τ b outer inner ho hi k s)
    (originalLeftCompactSectorNorm_nonneg N f r τ b outer inner ho hi k s))
    (integratedMixedSectorNorm_nonneg N f r τ b outer inner ho hi k s cut))
    (integratedLeftCompactSectorNorm_nonneg N f r τ b outer inner ho hi k s cut)

/-- A single source selector and inner width for all separated mixed and
left sectors, all orders up to the requested finite order, and the actual
small-current interval. The full particle sum is negligible. -/
theorem mixed_left_sector_sum_littleO (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) :
    ∃ η₀ : ℝ,0<η₀ ∧ ∀ η : ℝ,0<η → η<η₀ →
      ∃ α₀ : ℝ,0<α₀ ∧ ∀ α : ℝ,0<α → α<α₀ →
      ∃ τ₀ : ℝ,0<τ₀ ∧ ∀ τ : ℝ,0<τ → τ<τ₀ →
      ∀ (order : ℕ) (outer cap : ℝ) (ho : 0<outer),0<cap →
      ∃ inner₀ : ℝ,0< inner₀ ∧ inner₀≤cap ∧ ∀ (inner : ℝ) (hi : 0< inner),inner≤ inner₀ →
      ∀ (k : ℕ) (β : ℝ),k≤order → 0<β →
      radialSeriesSmall (fun eps N => mixedLeftSectorNorm N (constructedSelector d.thetaB η α)
        (Real.exp (-d.c₀*eps)) τ d.thetaB outer inner ho hi k (radialParameter d.theta eps) (eps^β)) := by
  obtain ⟨ηM,hηM,hM⟩ := original_mixed_sector_sum_littleO d hcsmall
  obtain ⟨ηL,hηL,hL⟩ := original_left_compact_sector_sum_littleO d hcsmall
  obtain ⟨ηCM,hηCM,hCM⟩ := current_mixed_sector_sum_littleO d hcsmall
  obtain ⟨ηCL,hηCL,hCL⟩ := current_left_compact_sector_sum_littleO d hcsmall
  refine ⟨min ηM (min ηL (min ηCM ηCL)),lt_min hηM (lt_min hηL (lt_min hηCM hηCL)),?_⟩
  intro η hη hηlt
  obtain ⟨αM,hαM,hM⟩ := hM η hη (hηlt.trans_le (min_le_left _ _))
  obtain ⟨αL,hαL,hL⟩ := hL η hη (hηlt.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  obtain ⟨αCM,hαCM,hCM⟩ := hCM η hη
    (hηlt.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  obtain ⟨αCL,τCL,hαCL,hτCL,hCL⟩ := hCL η hη
    (hηlt.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  refine ⟨min αM (min αL (min αCM αCL)),lt_min hαM (lt_min hαL (lt_min hαCM hαCL)),?_⟩
  intro α hα hαlt
  have hαM' := hαlt.trans_le (min_le_left _ _)
  have hαL' := hαlt.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hαCM' := hαlt.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hαCL' := hαlt.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨τCM,hτCM,hCM⟩ := hCM α hα hαCM'
  refine ⟨min τCM τCL,lt_min hτCM hτCL,?_⟩
  intro τ hτ hτlt order outer cap ho hcap
  obtain ⟨iM,hiM,hiMcap,hM⟩ := hM α hα hαM' order outer cap ho hcap
  obtain ⟨iL,hiL,_hiLcap,hL⟩ := hL α hα hαL' order outer cap ho hcap
  obtain ⟨iCM,hiCM,_hiCMcap,hCM⟩ := hCM τ hτ (hτlt.trans_le (min_le_left _ _)) order outer cap ho hcap
  obtain ⟨iCL,hiCL,_hiCLcap,hCL⟩ := hCL α τ hα hαCL' hτ (hτlt.trans_le (min_le_right _ _)) order outer cap ho hcap
  refine ⟨min iM (min iL (min iCM iCL)),lt_min hiM (lt_min hiL (lt_min hiCM hiCL)),
    (min_le_left _ _).trans hiMcap,?_⟩
  intro inner hi hinner k β hk hβ
  have hM' := hM inner hi (hinner.trans (min_le_left _ _)) τ k hτ.le hk
  have hL' := hL inner hi (hinner.trans ((min_le_right _ _).trans (min_le_left _ _))) τ k hτ.le hk
  have hCM' := hCM inner hi
    (hinner.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))) k β hk hβ
  have hCL' := hCL inner hi
    (hinner.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))) k β hk hβ
  exact ((radialSeriesSmall.add hM' hL').add hCM').add hCL'

end
end IsingBulk.Tail
