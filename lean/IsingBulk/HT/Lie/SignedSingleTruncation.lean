import IsingBulk.HT.Lie.SignedTruncationLimit

/-! Single-guard physical normal form and true derivative limits. These
are the quantitative-sector interface; signed sector estimates supply
an actual integrable majorant, rather than an assumed derivative bound. -/
namespace IsingBulk.HT.Lie
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Jets IsingBulk.Lie IsingBulk.Tail
open MeasureTheory Set Filter Function
open scoped Topology ContDiff

theorem signed_single_truncation_derivatives_tendsto (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) :
    ∃ r : ℝ, 0 < r ∧ ∀ ε : ℝ, 0 < ε → ε ≤ r → ∀ α : ℝ,
      ∀ n M : ℕ, ∀ p q : Fin (n+1), p ≠ q → ∀ w : AngularSpace n → ℝ,
      ContDiff ℝ ∞ w → tsupport w ⊆ microcoreCube (n+1) r → ∀ j : ℕ,
      Tendsto (fun k => iteratedDeriv j
        (signedOriginalWeightedIntegral (Complex.exp (Complex.I*(α:ℂ))) n d ε
          (allBranchSingleTruncatedWeight M (allBranchTruncationScale k) p q w))
          (radialParameter d.theta ε)) atTop
        (𝓝 (iteratedDeriv j
          (signedOriginalWeightedIntegral (Complex.exp (Complex.I*(α:ℂ))) n d ε
            (fun u => w u*allBranchExteriorPairWeight M p q u))
          (radialParameter d.theta ε))) := by
  obtain ⟨rD,hrD,hdata⟩ := allBranchExterior_original_density_data d
  obtain ⟨a,rS,ha,hrS,hgap⟩ := signed_original_kernel_gap_and_floor d hcsmall
  let r := min rD rS
  have hr : 0 < r := lt_min hrD hrS
  refine ⟨r,hr,?_⟩
  intro ε hε hεr α n M p q hpq w hw hsupp j
  let K := microcoreCube (n+1) r
  have hK : IsCompact K := microcoreCube_compact (n+1) r
  have hub (u : AngularSpace n) (hu : u∈K) (i : Fin (n+1)) : |u i| ≤ r :=
    (mem_microcoreCube r u).mp hu i
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hw.continuous.continuousOn
  have hwB (u : AngularSpace n) (hu : u∈K) : |w u| ≤ max 0 C := by
    simpa only [Real.norm_eq_abs] using (hC u hu).trans (le_max_right 0 C)
  have hlimabs (u : AngularSpace n) : |w u*allBranchExteriorPairWeight M p q u| ≤ |w u| := by
    rw [abs_mul,abs_of_nonneg (allBranchExterior_pairWeight_nonneg M p q u)]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (allBranchExterior_pairWeight_le_one M p q hpq u) (abs_nonneg (w u))
  apply signed_weighted_derivatives_tendsto _ d ε hε _ K hK
    (fun u hu => (hdata ε hε (hεr.trans (min_le_left _ _)) n u
      (fun i => (hub u hu i).trans (min_le_left _ _))).1)
    (fun u hu => (hdata ε hε (hεr.trans (min_le_left _ _)) n u
      (fun i => (hub u hu i).trans (min_le_left _ _))).2)
    (fun u hu => (hgap ε hε (hεr.trans (min_le_right _ _)) α n u
      (fun i => (hub u hu i).trans (min_le_right _ _))).1)
    (fun k => allBranchSingleTruncatedWeight M (allBranchTruncationScale k) p q w)
    (fun u => w u*allBranchExteriorPairWeight M p q u)
    (fun k => (allBranchSingleTruncatedWeight_smooth M (allBranchTruncationScale_pos k) p q w hw).continuous.measurable)
    (hw.continuous.measurable.mul (allBranchExterior_pairWeight_measurable M p q))
    _ _ (le_max_left 0 C) _ _ _ j
  · intro k u hu
    apply hsupp (subset_tsupport w ?_)
    intro hz
    exact hu (by simp [allBranchSingleTruncatedWeight,hz])
  · intro u hu
    apply hsupp (subset_tsupport w ?_)
    exact (mul_ne_zero_iff.mp hu).1
  · intro k
    filter_upwards [ae_restrict_mem hK.measurableSet] with u hu
    exact (allBranchSingleTruncatedWeight_abs_le M _ p q hpq w u).trans (hwB u hu)
  · filter_upwards [ae_restrict_mem hK.measurableSet] with u hu
    exact (hlimabs u).trans (hwB u hu)
  · filter_upwards [ae_restrict_of_ae (allBranchExterior_ae_selected_distinct p q hpq)] with u hu
    apply tendsto_const_nhds.congr'
    filter_upwards [allBranchExterior_single_truncation_eventually M p q w u hu] with k hk
    exact hk.symm


theorem signed_single_truncated_normal_form (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) :
    ∃ r : ℝ, 0 < r ∧ ∀ ε : ℝ, 0 < ε → ε ≤ r → ∀ α : ℝ,
      ∀ n M : ℕ, ∀ p q : Fin (n+1), p ≠ q → ∀ h : ℝ, 0 < h →
      ∀ w : AngularSpace n → ℝ, ContDiff ℝ ∞ w →
      tsupport w ⊆ microcoreCube (n+1) r → ∀ j : ℕ,
      let W := allBranchSingleTruncatedWeight M h p q w
      iteratedDeriv j
        (signedOriginalWeightedIntegral (Complex.exp (Complex.I*(α:ℂ))) n d ε W)
          (radialParameter d.theta ε) = ((n+1).factorial:ℂ)⁻¹*∫ u : AngularSpace n,
          signedSourceTermSum (Complex.exp (Complex.I*(α:ℂ))) p q (-d.c₀*ε) d.thetaB W
            (unfactoredNumerator (fun t : ℂ × (Fin (n+1) → ℂ) => microRegularAmplitude t.1 t.2))
            j (radialParameter d.theta ε) u := by
  obtain ⟨rA,hrA,hchart⟩ := allBranchExterior_original_actual_chart d
  obtain ⟨C,rQ,_,hrQ,hnum⟩ := allBranchExterior_original_numerator_jets d 0
  obtain ⟨a,rS,ha,hrS,hgap⟩ := signed_original_kernel_gap_and_floor d hcsmall
  let r := min rA (min rQ rS)
  have hr : 0 < r := lt_min hrA (lt_min hrQ hrS)
  have hAr : r ≤ rA := min_le_left _ _
  have hQr : r ≤ rQ := (min_le_right _ _).trans (min_le_left _ _)
  have hSr : r ≤ rS := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨r,hr,?_⟩
  intro ε hε hεr α n M p q hpq h hh w hw hsupp j
  let W := allBranchSingleTruncatedWeight M h p q w
  have hsub : tsupport W ⊆ microcoreCube (n+1) r := by
    intro u hu
    exact hsupp (allBranchSingleTruncatedWeight_support M hh p q w hu).1
  have hcompact : HasCompactSupport W :=
    (microcoreCube_compact (n+1) r).of_isClosed_subset (isClosed_tsupport _) hsub
  have hpoint (u : AngularSpace n) (hu : u∈tsupport W) :
      ActualJetPoint (-d.c₀*ε) d.thetaB p q (radialParameter d.theta ε) u ∧
      AnalyticAt ℂ (unfactoredNumerator (fun t : ℂ × (Fin (n+1) → ℂ) => microRegularAmplitude t.1 t.2))
        (radialParameter d.theta ε,chartMap (-d.c₀*ε) d.thetaB (radialParameter d.theta ε) u) := by
    have hub := (mem_microcoreCube r u).mp (hsub hu)
    have hupq : u p ≠ u q := by
      have hδ := (allBranchSingleTruncatedWeight_support M hh p q w hu).2
      intro he
      rw [he,sub_self,abs_zero] at hδ
      linarith
    refine ⟨hchart ε hε (hεr.trans hAr) n p q u
      (fun i => (hub i).trans hAr) hupq,?_⟩
    have hn := (hnum ε hε (hεr.trans hQr) (n+1) u (fun i => (hub i).trans hQr)).analytic
    simpa only [original_chartMap_eq] using hn
  apply signed_physical_compact_source_derivative _ d ε hε p q hpq W
    (allBranchSingleTruncatedWeight_smooth M hh p q w hw) hcompact _
    (fun u hu => (hpoint u hu).1) (fun u hu => (hpoint u hu).2) _ j
  intro u hu
  exact (hgap ε hε (hεr.trans hSr) α n u
    (fun i => ((mem_microcoreCube r u).mp (hsub hu) i).trans hSr)).1

/-- Exact excision endpoint for the single selected guard. The finite
semantic Lie integrals converge to the true derivative of the unguarded
physical integral. This does not assume a selected-tube flux limit or
interchange a puncture limit with the radial limit or particle sum. -/
theorem signed_single_truncated_source_integrals_tendsto (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) :
    ∃ r : ℝ, 0 < r ∧ ∀ ε : ℝ, 0 < ε → ε ≤ r → ∀ α : ℝ,
      ∀ n M : ℕ, ∀ p q : Fin (n+1), p ≠ q →
      ∀ w : AngularSpace n → ℝ, ContDiff ℝ ∞ w →
      tsupport w ⊆ microcoreCube (n+1) r → ∀ j : ℕ,
      Tendsto (fun k => ((n+1).factorial:ℂ)⁻¹*∫ u : AngularSpace n,
        signedSourceTermSum (Complex.exp (Complex.I*(α:ℂ))) p q
          (-d.c₀*ε) d.thetaB
          (allBranchSingleTruncatedWeight M (allBranchTruncationScale k) p q w)
          (unfactoredNumerator
            (fun z : ℂ × (Fin (n+1) → ℂ) => microRegularAmplitude z.1 z.2))
          j (radialParameter d.theta ε) u) atTop
        (𝓝 (iteratedDeriv j
          (signedOriginalWeightedIntegral (Complex.exp (Complex.I*(α:ℂ))) n d ε
            (fun u => w u*allBranchExteriorPairWeight M p q u))
          (radialParameter d.theta ε))) := by
  obtain ⟨rI,hrI,hI⟩ := signed_single_truncated_normal_form d hcsmall
  obtain ⟨rL,hrL,hL⟩ := signed_single_truncation_derivatives_tendsto d hcsmall
  let r := min rI rL
  refine ⟨r,lt_min hrI hrL,?_⟩
  intro ε hε hεr α n M p q hpq w hw hsupp j
  have hsI : tsupport w ⊆ microcoreCube (n+1) rI := by
    intro u hu
    exact (mem_microcoreCube rI u).mpr (fun i =>
      ((mem_microcoreCube r u).mp (hsupp hu) i).trans (min_le_left _ _))
  have hsL : tsupport w ⊆ microcoreCube (n+1) rL := by
    intro u hu
    exact (mem_microcoreCube rL u).mpr (fun i =>
      ((mem_microcoreCube r u).mp (hsupp hu) i).trans (min_le_right _ _))
  apply (hL ε hε (hεr.trans (min_le_right _ _)) α n M p q hpq w hw hsL j).congr
  intro k
  exact hI ε hε (hεr.trans (min_le_left _ _)) α n M p q hpq
    (allBranchTruncationScale k) (allBranchTruncationScale_pos k) w hw hsI j

end
end IsingBulk.HT.Lie
