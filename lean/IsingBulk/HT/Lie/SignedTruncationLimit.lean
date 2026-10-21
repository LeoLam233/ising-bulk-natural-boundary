import IsingBulk.HT.Lie.SignedWeightedIntegral
import IsingBulk.Tail.AllBranchExteriorTruncationIntegralLimit

/-! Removal of both genuine real excision cutoffs in the signed physical
integral. The limit is proved at every true parameter derivative order by
analytic compact domination. It does not assume a vanishing-flux certificate,
a derivative identity, or a majorant for the differentiated Lie descendants. -/
namespace IsingBulk.HT.Lie
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Jets IsingBulk.Lie IsingBulk.Tail
open MeasureTheory Set Filter Function
open scoped Topology ContDiff

/-- Both actual guards have absolute value at most one. -/
theorem fullTruncatedWeight_abs_le {N : ℕ} (M : ℕ) (h : ℝ)
    (p q : Fin N) (hpq : p ≠ q) (w : (Fin N → ℝ) → ℝ) (u : Fin N → ℝ) :
    |allBranchTruncatedWeight M h p q w u| ≤ |w u| := by
  have he : allBranchTruncatedWeight M h p q w u =
      allBranchSingleTruncatedWeight M h p q w u*branchFarCutoff h u := by
    unfold allBranchTruncatedWeight allBranchTruncationGate
      allBranchSingleTruncatedWeight allBranchGuardedPairWeight
    ring
  have hf : 0 ≤ branchFarCutoff h u ∧ branchFarCutoff h u ≤ 1 :=
    thresholdStep_range _ _ _
  rw [he,abs_mul,abs_of_nonneg hf.1]
  exact (mul_le_mul_of_nonneg_left hf.2 (abs_nonneg _)).trans
    (by simpa only [mul_one] using allBranchSingleTruncatedWeight_abs_le M h p q hpq w u)

/-- Actual signed source jets converge pointwise away from the selected
null diagonal; the fixed real cutoff is the only varying factor. -/
theorem signed_truncated_source_sums_eventually {n : ℕ} (σ : ℂ) (M : ℕ)
    (p q : Fin (n+1)) (w : AngularSpace n → ℝ) (u : AngularSpace n) (hu : u p ≠ u q)
    (v θ : ℝ) (Q : ℂ × (Fin (n+1) → ℂ) → ℂ) :
    ∀ᶠ k in atTop, ∀ j : ℕ, ∀ s : ℂ,
      signedSourceTermSum σ p q v θ
        (allBranchTruncatedWeight M (allBranchTruncationScale k) p q w) Q j s u =
      signedSourceTermSum σ p q v θ
        (fun x => w x*allBranchExteriorPairWeight M p q x) Q j s u := by
  filter_upwards [allBranchExterior_truncated_jets_eventually M p q w u hu] with k hk
  intro j s
  unfold signedSourceTermSum
  congr 1
  apply List.map_congr_left
  intro T _
  simp only [signedSourceValue,hk T.cutoff]

theorem signed_truncated_source_sums_ae_tendsto {n : ℕ} (σ : ℂ) (M : ℕ)
    (p q : Fin (n+1)) (hpq : p ≠ q) (w : AngularSpace n → ℝ) (v θ : ℝ)
    (Q : ℂ × (Fin (n+1) → ℂ) → ℂ) (j : ℕ) (s : ℂ) :
    ∀ᵐ u : AngularSpace n, Tendsto
      (fun k => signedSourceTermSum σ p q v θ
        (allBranchTruncatedWeight M (allBranchTruncationScale k) p q w) Q j s u)
      atTop (𝓝 (signedSourceTermSum σ p q v θ
        (fun x => w x*allBranchExteriorPairWeight M p q x) Q j s u)) := by
  filter_upwards [allBranchExterior_ae_selected_distinct p q hpq] with u hu
  apply tendsto_const_nhds.congr'
  filter_upwards [signed_truncated_source_sums_eventually σ M p q w u hu v θ Q] with k hk
  exact (hk j s).symm

/-- Simultaneous selected-pair and full-collision excision removal for the
true signed physical parameter derivatives. The radius is chosen before N,
the phase sign, the differentiation order, and the excision sequence. -/
theorem signed_full_truncation_derivatives_tendsto (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) :
    ∃ r : ℝ, 0 < r ∧ ∀ ε : ℝ, 0 < ε → ε ≤ r → ∀ α : ℝ,
      ∀ n M : ℕ, ∀ p q : Fin (n+1), p ≠ q → ∀ w : AngularSpace n → ℝ,
      ContDiff ℝ ∞ w → tsupport w ⊆ microcoreCube (n+1) r → ∀ j : ℕ,
      Tendsto (fun k => iteratedDeriv j
        (signedOriginalWeightedIntegral (Complex.exp (Complex.I*(α:ℂ))) n d ε
          (allBranchTruncatedWeight M (allBranchTruncationScale k) p q w))
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
    (fun k => allBranchTruncatedWeight M (allBranchTruncationScale k) p q w)
    (fun u => w u*allBranchExteriorPairWeight M p q u)
    (fun k => (allBranchTruncatedWeight_smooth M (allBranchTruncationScale_pos k) p q w hw).continuous.measurable)
    (hw.continuous.measurable.mul (allBranchExterior_pairWeight_measurable M p q))
    _ _ (le_max_left 0 C) _ _ _ j
  · intro k u hu
    apply hsupp (subset_tsupport w ?_)
    intro hz
    exact hu (by simp [allBranchTruncatedWeight,allBranchTruncationGate,hz])
  · intro u hu
    apply hsupp (subset_tsupport w ?_)
    exact (mul_ne_zero_iff.mp hu).1
  · intro k
    filter_upwards [ae_restrict_mem hK.measurableSet] with u hu
    exact (fullTruncatedWeight_abs_le M _ p q hpq w u).trans (hwB u hu)
  · filter_upwards [ae_restrict_mem hK.measurableSet] with u hu
    exact (hlimabs u).trans (hwB u hu)
  · filter_upwards [ae_restrict_of_ae (allBranchExterior_ae_selected_distinct p q hpq)] with u hu
    apply tendsto_const_nhds.congr'
    filter_upwards [allBranchExterior_truncation_germ_eventually M p q w u hu] with k hk
    exact hk.eq_of_nhds.symm

/-- Exact physical derivative identity for each genuine smooth excision. -/
theorem signed_physical_truncated_derivative_identity (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) :
    ∃ r : ℝ, 0 < r ∧ ∀ ε : ℝ, 0 < ε → ε ≤ r → ∀ α : ℝ,
      ∀ n M : ℕ, ∀ p q : Fin (n+1), p ≠ q → ∀ h : ℝ, 0 < h →
      ∀ w : AngularSpace n → ℝ, ContDiff ℝ ∞ w →
      tsupport w ⊆ microcoreCube (n+1) r → ∀ j : ℕ,
      iteratedDeriv j
        (signedOriginalWeightedIntegral (Complex.exp (Complex.I*(α:ℂ))) n d ε
          (allBranchTruncatedWeight M h p q w)) (radialParameter d.theta ε) =
        ((n+1).factorial:ℂ)⁻¹*∫ u,
          signedSourceTermSum (Complex.exp (Complex.I*(α:ℂ))) p q (-d.c₀*ε) d.thetaB
            (allBranchTruncatedWeight M h p q w)
            (unfactoredNumerator (fun z : ℂ × (Fin (n+1) → ℂ) => microRegularAmplitude z.1 z.2))
            j (radialParameter d.theta ε) u := by
  obtain ⟨rD,hrD,hdata⟩ := allBranchExterior_truncated_source_data d
  obtain ⟨a,rS,ha,hrS,hgap⟩ := signed_original_kernel_gap_and_floor d hcsmall
  let r := min rD rS
  have hr : 0 < r := lt_min hrD hrS
  refine ⟨r,hr,?_⟩
  intro ε hε hεr α n M p q hpq h hh w hw hsupp j
  have hsD : tsupport w ⊆ microcoreCube (n+1) rD := by
    intro u hu
    exact (mem_microcoreCube rD u).mpr (fun i =>
      ((mem_microcoreCube r u).mp (hsupp hu) i).trans (min_le_left _ _))
  obtain ⟨hsmooth,hcompact,hpoint⟩ := hdata ε hε (hεr.trans (min_le_left _ _))
    n M p q h hh w hw hsD
  apply signed_physical_compact_source_derivative _ d ε hε p q hpq _ hsmooth hcompact _
    (fun u hu => (hpoint u hu).1) (fun u hu => (hpoint u hu).2) _ j
  intro u hu
  have hub := (mem_microcoreCube r u).mp
    (hsupp (allBranchTruncatedWeight_support M hh p q w hu).1)
  exact (hgap ε hε (hεr.trans (min_le_right _ _)) α n u
    (fun i => (hub i).trans (min_le_right _ _))).1

/-- The actual punctured signed Lie integrals converge to the exact physical
parameter derivative. This closes the qualitative cutoff-removal direction
without postulating convergence of boundary fluxes or differentiated densities. -/
theorem signed_lie_integrals_tendsto_physical_derivative (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) :
    ∃ r : ℝ, 0 < r ∧ ∀ ε : ℝ, 0 < ε → ε ≤ r → ∀ α : ℝ,
      ∀ n M : ℕ, ∀ p q : Fin (n+1), p ≠ q → ∀ w : AngularSpace n → ℝ,
      ContDiff ℝ ∞ w → tsupport w ⊆ microcoreCube (n+1) r → ∀ j : ℕ,
      Tendsto (fun k => ((n+1).factorial:ℂ)⁻¹*∫ u,
        signedSourceTermSum (Complex.exp (Complex.I*(α:ℂ))) p q (-d.c₀*ε) d.thetaB
          (allBranchTruncatedWeight M (allBranchTruncationScale k) p q w)
          (unfactoredNumerator (fun z : ℂ × (Fin (n+1) → ℂ) => microRegularAmplitude z.1 z.2))
          j (radialParameter d.theta ε) u) atTop
        (𝓝 (iteratedDeriv j
          (signedOriginalWeightedIntegral (Complex.exp (Complex.I*(α:ℂ))) n d ε
            (fun u => w u*allBranchExteriorPairWeight M p q u))
          (radialParameter d.theta ε))) := by
  obtain ⟨rI,hrI,hI⟩ := signed_physical_truncated_derivative_identity d hcsmall
  obtain ⟨rL,hrL,hL⟩ := signed_full_truncation_derivatives_tendsto d hcsmall
  let r := min rI rL
  have hr : 0 < r := lt_min hrI hrL
  refine ⟨r,hr,?_⟩
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
