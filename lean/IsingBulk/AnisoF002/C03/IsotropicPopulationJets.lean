import IsingBulk.AnisoF002.C03.RegularIsotropicPopulationSplit
import IsingBulk.AnisoF002.C03.IsotropicRightCutoffProducts
import IsingBulk.AnisoF002.C03.IsotropicBalancedMatrixJets

/-!
# Real angular jets of the actual population partition

The outer transition has a fixed compact transition interval.  Its composition
with each raw population is controlled before the particle number is chosen.
These are the literal population weights introduced after the full homotopy.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set Filter
open scoped Topology BigOperators

theorem populationTransition_finiteJetControl (k : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ FiniteJetControl k populationTransition C := by
  have hb (m : ℕ) : ∃ C : ℝ, 1 ≤ C ∧
      ∀ x : ℝ, ‖iteratedFDeriv ℝ m populationTransition x‖ ≤ C := by
    obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
      (f := iteratedFDeriv ℝ m populationTransition)
      (populationTransition_contDiff (j := m)).continuous_iteratedFDeriv'.continuousOn
    refine ⟨max 1 C, le_max_left _ _, ?_⟩
    intro x
    by_cases hx : x ∈ Icc (0 : ℝ) 1
    · exact (hC x hx).trans (le_max_right _ _)
    by_cases hm : m = 0
    · subst m
      rw [norm_iteratedFDeriv_zero, Real.norm_of_nonneg (populationTransition_bounds x).1]
      exact (populationTransition_bounds x).2.trans (le_max_left _ _)
    have hc : ∃ c : ℝ, populationTransition =ᶠ[𝓝 x] fun _ => c := by
      by_cases hx0 : x < 0
      · refine ⟨0, ?_⟩
        filter_upwards [gt_mem_nhds (show x < (1 / 4 : ℝ) by linarith)] with y hy
        exact populationTransition_zero hy.le
      · have hx1 : 1 < x := by
          have : ¬ (0 ≤ x ∧ x ≤ 1) := hx
          push Not at this
          exact this (le_of_not_gt hx0)
        refine ⟨1, ?_⟩
        filter_upwards [lt_mem_nhds (show (1 / 2 : ℝ) < x by linarith)] with y hy
        exact populationTransition_one hy.le
    obtain ⟨c, hc⟩ := hc
    rw [(hc.iteratedFDeriv ℝ m).eq_of_nhds, iteratedFDeriv_const_of_ne hm]
    change ‖(0 : (ℝ [×m]→L[ℝ] ℝ))‖ ≤ max 1 C
    rw [norm_zero]
    exact (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left _ _)
  choose C hC hB using hb
  let L := 1 + ∑ m ∈ Finset.range (k + 1), C m
  have hC0 (m : ℕ) : 0 ≤ C m := zero_le_one.trans (hC m)
  have hL : 1 ≤ L := by
    dsimp [L]
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun m _ => hC0 m))
  refine ⟨L, hL, populationTransition_contDiff, ?_⟩
  intro m hm x
  have hh : C m ≤ ∑ i ∈ Finset.range (k + 1), C i :=
    Finset.single_le_sum (fun i _ => hC0 i) (Finset.mem_range.mpr (Nat.lt_succ_of_le hm))
  exact (hB m x).trans (by dsimp [L]; linarith)

theorem FiniteJetControl.comp_power_bound
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {k : ℕ} {f : E → F} {g : F → G} {C D : ℝ}
    (hf : FiniteJetControl k f D) (hg : FiniteJetControl k g C)
    (hC : 0 ≤ C) (hD : 1 ≤ D) :
    FiniteJetControl k (g ∘ f) ((k.factorial : ℝ) * C * D ^ k) := by
  refine ⟨hg.smooth.comp hf.smooth, ?_⟩
  intro m hm x
  have hh := norm_iteratedFDeriv_comp_at_le f g x m
    (hf.smooth.of_le (by exact_mod_cast hm)).contDiffAt
    (hg.smooth.of_le (by exact_mod_cast hm)).contDiffAt C D
    (fun i hi => hg.bound i (hi.trans hm) (f x))
    (fun i hi him => (hf.bound i (him.trans hm) x).trans
      (by simpa only [pow_one] using pow_le_pow_right₀ hD hi))
  exact hh.trans (mul_le_mul
    (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.factorial_le hm) hC)
    (pow_le_pow_right₀ hD hm) (pow_nonneg (zero_le_one.trans hD) _) (by positivity))

theorem actual_population_finiteJetControl (η : ℝ) (k : ℕ) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ N : ℕ,
      FiniteJetControl k (@actualUpperPopulation N η) ((N : ℝ) * L) ∧
      FiniteJetControl k (@actualLowerPopulation N η) ((N : ℝ) * L) := by
  obtain ⟨L, hL, hp, hm, _, _⟩ := actual_bump_global_jet_control η k
  refine ⟨L, hL, ?_⟩
  intro N
  have hcoord (f : ℝ → ℝ) (hf : FiniteJetControl k f L) (i : Fin N) :
      FiniteJetControl k (fun θ : Fin N → ℝ => f (θ i)) L :=
    hf.comp_clm (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => ℝ) i)
      (norm_real_coordinate_projection_le_one i)
  constructor
  · have hh := finiteJetControl_finsetSum (Finset.univ : Finset (Fin N)) k
      (fun i (θ : Fin N → ℝ) => upperPeriodicBump η (θ i)) (fun _ => L)
      (fun i _ => hcoord _ hp i)
    change FiniteJetControl k (fun θ : Fin N → ℝ => ∑ i, upperPeriodicBump η (θ i)) _
    simpa only [Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] using hh
  · have hh := finiteJetControl_finsetSum (Finset.univ : Finset (Fin N)) k
      (fun i (θ : Fin N → ℝ) => lowerPeriodicBump η (θ i)) (fun _ => L)
      (fun i _ => hcoord _ hm i)
    change FiniteJetControl k (fun θ : Fin N → ℝ => ∑ i, lowerPeriodicBump η (θ i)) _
    simpa only [Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] using hh

theorem actual_population_transition_jets (η : ℝ) (k : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ N : ℕ, 0 < N →
      FiniteJetControl k (fun θ : Fin N → ℝ =>
        (populationTransition (actualUpperPopulation η θ) : ℂ)) (C * (N : ℝ) ^ k) ∧
      FiniteJetControl k (fun θ : Fin N → ℝ =>
        (populationTransition (actualLowerPopulation η θ) : ℂ)) (C * (N : ℝ) ^ k) := by
  obtain ⟨L, hL, hpop⟩ := actual_population_finiteJetControl η k
  obtain ⟨A, hA, htrans⟩ := populationTransition_finiteJetControl k
  let C := (k.factorial : ℝ) * A * L ^ k
  have hfac : (1 : ℝ) ≤ k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hC : 1 ≤ C := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le hfac hA) (one_le_pow₀ hL)
  refine ⟨C, hC, ?_⟩
  intro N hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hD : 1 ≤ (N : ℝ) * L := one_le_mul_of_one_le_of_one_le hN1 hL
  have hc (f : (Fin N → ℝ) → ℝ) (hf : FiniteJetControl k f ((N : ℝ) * L)) :
      FiniteJetControl k (fun θ => (populationTransition (f θ) : ℂ)) (C * (N : ℝ) ^ k) := by
    have hh := (hf.comp_power_bound htrans (zero_le_one.trans hA) hD).clm Complex.ofRealCLM
    have hnorm : ‖Complex.ofRealCLM‖ = 1 := Complex.ofRealLI.norm_toContinuousLinearMap
    simp only [hnorm, one_mul, Function.comp_def, Complex.ofRealCLM_apply] at hh
    convert hh using 1
    dsimp [C]
    rw [mul_pow]
    ring
  exact ⟨hc _ (hpop N).1, hc _ (hpop N).2⟩

end
end IsingBulk.AnisoF002.Isotropic
