import IsingBulk.AnisoF002.C03.IsotropicPeriodicBumpJets
import IsingBulk.AnisoF002.C03.IsotropicPhysicalDensity

/-!
# All real angular jets of the complete balanced matrix

Every population derivative is included. Before any particle number is
chosen, each fixed derivative budget has a polynomial bound for every
entry of the actual full matrix. This is the smooth input to inversion.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators Matrix
open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem FiniteJetControl.complex_const_mul {k : ℕ} {f : E → ℂ} {C : ℝ}
    (hf : FiniteJetControl k f C) (a : ℂ) :
    FiniteJetControl k (fun x => a * f x) (‖a‖ * C) := by
  refine ⟨contDiff_const.mul hf.smooth, ?_⟩
  intro m hm x
  change ‖iteratedFDeriv ℝ m (fun y => a • f y) x‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply' (hf.smooth.of_le (by exact_mod_cast hm)).contDiffAt,
    norm_smul]
  exact mul_le_mul_of_nonneg_left (hf.bound m hm x) (norm_nonneg _)

theorem FiniteJetControl.complex_mul_const {k : ℕ} {f : E → ℂ} {C : ℝ}
    (hf : FiniteJetControl k f C) (a : ℂ) :
    FiniteJetControl k (fun x => f x * a) (‖a‖ * C) := by
  simpa only [mul_comm] using hf.complex_const_mul a

theorem actualBalancedMatrix_entry {N : ℕ} (η τ ξ : ℝ) (θ : Fin N → ℝ) (i j : Fin N) :
    actualBalancedMatrix η τ ξ θ i j =
      (Pi.single j 1 : Fin N → ℂ) i - Complex.I * (((ξ * τ) / (N : ℝ) : ℝ) : ℂ) *
        ((((deriv (upperPeriodicBump η) (θ j) : ℝ) : ℂ) * (lowerPeriodicBump η (θ i) : ℂ) +
            (∑ l, (upperPeriodicBump η (θ l) : ℂ)) * ((deriv (lowerPeriodicBump η) (θ i) : ℝ) : ℂ) *
              (Pi.single j 1 : Fin N → ℂ) i) -
          (((deriv (lowerPeriodicBump η) (θ j) : ℝ) : ℂ) * (upperPeriodicBump η (θ i) : ℂ) +
            (∑ l, (lowerPeriodicBump η (θ l) : ℂ)) * ((deriv (upperPeriodicBump η) (θ i) : ℝ) : ℂ) *
              (Pi.single j 1 : Fin N → ℂ) i)) := by
  change (Pi.single j 1 : Fin N → ℂ) i - Complex.I *
    balancedDisplacementDifferential ((ξ * τ) / Fintype.card (Fin N))
      (fun l => upperPeriodicBump η (θ l)) (fun l => lowerPeriodicBump η (θ l))
      (fun l => deriv (upperPeriodicBump η) (θ l))
      (fun l => deriv (lowerPeriodicBump η) (θ l)) (Pi.single j 1) i = _
  simp only [balancedDisplacementDifferential, Fintype.card_fin, Complex.ofReal_sum]
  simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]
  ring

theorem exists_actual_balanced_matrix_jet_control (η : ℝ) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 0 < N →
      ∀ τ ξ : ℝ, τ ∈ Icc 0 1 → ξ ∈ Icc 0 1 → ∀ i j : Fin N,
        FiniteJetControl k (fun θ : Fin N → ℝ => actualBalancedMatrix η τ ξ θ i j) (C * N) := by
  obtain ⟨L, hL, hp, hm, hdp, hdm⟩ := actual_bump_global_jet_control η k
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  let C := 1 + 4 * 2 ^ k * L ^ 2
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro N hN τ ξ hτ hξ i j
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  let p : Fin N → (Fin N → ℝ) → ℂ := fun l θ => (upperPeriodicBump η (θ l) : ℂ)
  let m : Fin N → (Fin N → ℝ) → ℂ := fun l θ => (lowerPeriodicBump η (θ l) : ℂ)
  let dp : Fin N → (Fin N → ℝ) → ℂ := fun l θ => ((deriv (upperPeriodicBump η) (θ l) : ℝ) : ℂ)
  let dm : Fin N → (Fin N → ℝ) → ℂ := fun l θ => ((deriv (lowerPeriodicBump η) (θ l) : ℝ) : ℂ)
  have hp' (l : Fin N) : FiniteJetControl k (p l) L := finiteJetControl_complex_coordinate hp l
  have hm' (l : Fin N) : FiniteJetControl k (m l) L := finiteJetControl_complex_coordinate hm l
  have hdp' (l : Fin N) : FiniteJetControl k (dp l) L := finiteJetControl_complex_coordinate hdp l
  have hdm' (l : Fin N) : FiniteJetControl k (dm l) L := finiteJetControl_complex_coordinate hdm l
  have hP : FiniteJetControl k (fun θ => ∑ l, p l θ) ((N : ℝ) * L) := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
      finiteJetControl_finsetSum Finset.univ k p (fun _ => L) (fun l _ => hp' l)
  have hQ : FiniteJetControl k (fun θ => ∑ l, m l θ) ((N : ℝ) * L) := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
      finiteJetControl_finsetSum Finset.univ k m (fun _ => L) (fun l _ => hm' l)
  let e : ℂ := (Pi.single j 1 : Fin N → ℂ) i
  have he : ‖e‖ ≤ 1 := by dsimp [e]; by_cases hij : j = i <;> simp [hij]
  let H := (2 : ℝ) ^ k * L ^ 2
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have h₁ : FiniteJetControl k (fun θ => dp j θ * m i θ) H := by
    convert (hdp' j).mul (hm' i) hL0 hL0 using 1
    dsimp [H]
    ring
  have h₂ : FiniteJetControl k (fun θ => (∑ l, p l θ) * dm i θ * e) ((N : ℝ) * H) := by
    have hh := (hP.mul (hdm' i) (by positivity) hL0).complex_mul_const e
    apply hh.mono_bound
    calc
      ‖e‖ * (2 ^ k * ((N : ℝ) * L) * L) ≤ 1 * (2 ^ k * ((N : ℝ) * L) * L) :=
        mul_le_mul_of_nonneg_right he (by positivity)
      _ = _ := by dsimp [H]; ring
  have h₃ : FiniteJetControl k (fun θ => dm j θ * p i θ) H := by
    convert (hdm' j).mul (hp' i) hL0 hL0 using 1
    dsimp [H]
    ring
  have h₄ : FiniteJetControl k (fun θ => (∑ l, m l θ) * dp i θ * e) ((N : ℝ) * H) := by
    have hh := (hQ.mul (hdp' i) (by positivity) hL0).complex_mul_const e
    apply hh.mono_bound
    calc
      ‖e‖ * (2 ^ k * ((N : ℝ) * L) * L) ≤ 1 * (2 ^ k * ((N : ℝ) * L) * L) :=
        mul_le_mul_of_nonneg_right he (by positivity)
      _ = _ := by dsimp [H]; ring
  have hinside := (h₁.add h₂).sub (h₃.add h₄)
  let a : ℂ := Complex.I * (((ξ * τ) / (N : ℝ) : ℝ) : ℂ)
  have ha : ‖a‖ ≤ 1 := by
    dsimp [a]
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (mul_nonneg hξ.1 hτ.1) hNr.le)]
    apply (div_le_iff₀ hNr).mpr
    nlinarith only [hξ.1, hξ.2, hτ.1, hτ.2, hN1]
  have hfull := (finiteJetControl_const k e 1 he).sub (hinside.complex_const_mul a)
  have hfull' : FiniteJetControl k
      (fun θ => e - a * ((dp j θ * m i θ + (∑ l, p l θ) * dm i θ * e) -
        (dm j θ * p i θ + (∑ l, m l θ) * dp i θ * e))) (C * N) := by
    apply hfull.mono_bound
    calc
      1 + ‖a‖ * (H + (N : ℝ) * H + (H + (N : ℝ) * H)) ≤
          1 + (H + (N : ℝ) * H + (H + (N : ℝ) * H)) := by
        exact add_le_add le_rfl (mul_le_of_le_one_left (by positivity) ha)
      _ ≤ C * N := by
        have hh : H ≤ (N : ℝ) * H := le_mul_of_one_le_left hH hN1
        dsimp [C, H] at *
        nlinarith only [hh, hN1]
  have heq : (fun θ : Fin N → ℝ => actualBalancedMatrix η τ ξ θ i j) =
      (fun θ => e - a * ((dp j θ * m i θ + (∑ l, p l θ) * dm i θ * e) -
        (dm j θ * p i θ + (∑ l, m l θ) * dp i θ * e))) := by
    funext θ
    rw [actualBalancedMatrix_entry]
  rw [heq]
  exact hfull'

end IsingBulk.AnisoF002.Isotropic
