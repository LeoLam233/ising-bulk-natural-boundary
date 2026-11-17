import IsingBulk.AnisoF002.C03.IsotropicFiniteJetControl
import IsingBulk.AnisoF002.C03.IsotropicActualJacobian
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# All fixed real jets of the actual periodic bumps

Periodicity and compactness supply bounds for every finite derivative
budget, before any particle number is chosen. Coordinate projections
preserve those bounds in every angular dimension.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators
open Set

theorem periodic_iteratedDeriv_F002 (f : ℝ → ℝ) (c : ℝ)
    (hp : Function.Periodic f c) (k : ℕ) : Function.Periodic (iteratedDeriv k f) c := by
  induction k with
  | zero => simpa only [iteratedDeriv_zero] using hp
  | succ k ih =>
    rw [iteratedDeriv_succ]
    exact periodic_deriv_F002 _ _ ih

theorem periodic_finiteJetControl (f : ℝ → ℝ) (c : ℝ) (hc : c ≠ 0)
    (hp : Function.Periodic f c) (hf : ∀ m : ℕ, ContDiff ℝ m f) (k : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ FiniteJetControl k f C := by
  have hbound (m : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖iteratedFDeriv ℝ m f x‖ ≤ C := by
    have hk := (periodic_iteratedDeriv_F002 f c hp m).compact_of_continuous hc
      ((hf m).continuous_iteratedDeriv' m)
    obtain ⟨C, hC⟩ := hk.exists_bound_of_continuousOn (f := id) continuousOn_id
    refine ⟨max 0 C, le_max_left _ _, ?_⟩
    intro x
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    exact (hC (iteratedDeriv m f x) (mem_range_self x)).trans (le_max_right _ _)
  choose C hC0 hC using hbound
  let L := 1 + ∑ m ∈ Finset.range (k + 1), C m
  have hsum : 0 ≤ ∑ m ∈ Finset.range (k + 1), C m := Finset.sum_nonneg (fun m _ => hC0 m)
  refine ⟨L, by dsimp [L]; linarith only [hsum], hf k, ?_⟩
  intro m hm x
  have hh : C m ≤ ∑ i ∈ Finset.range (k + 1), C i :=
    Finset.single_le_sum (fun i _ => hC0 i) (Finset.mem_range.mpr (Nat.lt_succ_of_le hm))
  exact (hC m x).trans (by dsimp [L]; linarith only [hh])

theorem actual_bump_global_jet_control (η : ℝ) (k : ℕ) :
    ∃ L : ℝ, 1 ≤ L ∧
      FiniteJetControl k (upperPeriodicBump η) L ∧
      FiniteJetControl k (lowerPeriodicBump η) L ∧
      FiniteJetControl k (deriv (upperPeriodicBump η)) L ∧
      FiniteJetControl k (deriv (lowerPeriodicBump η)) L := by
  have hc : 2 * Real.pi ≠ 0 := by positivity
  obtain ⟨C₁, hC₁, hp⟩ := periodic_finiteJetControl (upperPeriodicBump η) _ hc
    (upperPeriodicBump_periodic η) (fun m => upperPeriodicBump_contDiff η (n := m)) k
  obtain ⟨C₂, _, hm⟩ := periodic_finiteJetControl (lowerPeriodicBump η) _ hc
    (lowerPeriodicBump_periodic η) (fun m => lowerPeriodicBump_contDiff η (n := m)) k
  obtain ⟨C₃, _, hdp⟩ := periodic_finiteJetControl (deriv (upperPeriodicBump η)) _ hc
    (periodic_deriv_F002 _ _ (upperPeriodicBump_periodic η))
    (fun m => (upperPeriodicBump_contDiff η (n := m + 1)).deriv') k
  obtain ⟨C₄, _, hdm⟩ := periodic_finiteJetControl (deriv (lowerPeriodicBump η)) _ hc
    (periodic_deriv_F002 _ _ (lowerPeriodicBump_periodic η))
    (fun m => (lowerPeriodicBump_contDiff η (n := m + 1)).deriv') k
  let L := max (max C₁ C₂) (max C₃ C₄)
  have h₁ : C₁ ≤ L := (le_max_left _ _).trans (le_max_left _ _)
  have h₂ : C₂ ≤ L := (le_max_right _ _).trans (le_max_left _ _)
  have h₃ : C₃ ≤ L := (le_max_left _ _).trans (le_max_right _ _)
  have h₄ : C₄ ≤ L := (le_max_right _ _).trans (le_max_right _ _)
  exact ⟨L, hC₁.trans h₁, hp.mono_bound h₁, hm.mono_bound h₂,
    hdp.mono_bound h₃, hdm.mono_bound h₄⟩

theorem norm_real_coordinate_projection_le_one {N : ℕ} (i : Fin N) :
    ‖(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => ℝ) i)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  simpa only [ContinuousLinearMap.proj_apply, one_mul] using norm_le_pi_norm v i

theorem finiteJetControl_complex_coordinate {k N : ℕ} {f : ℝ → ℝ} {L : ℝ}
    (hf : FiniteJetControl k f L) (i : Fin N) :
    FiniteJetControl k (fun θ : Fin N → ℝ => (f (θ i) : ℂ)) L := by
  have hp := hf.comp_clm (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => ℝ) i)
    (norm_real_coordinate_projection_le_one i)
  have hh := hp.clm Complex.ofRealCLM
  have hnorm : ‖Complex.ofRealCLM‖ = 1 := Complex.ofRealLI.norm_toContinuousLinearMap
  simpa only [ContinuousLinearMap.proj_apply, Complex.ofRealCLM_apply,
    hnorm, one_mul] using hh

end IsingBulk.AnisoF002.Isotropic
