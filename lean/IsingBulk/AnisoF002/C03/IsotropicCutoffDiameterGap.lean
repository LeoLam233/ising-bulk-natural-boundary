import IsingBulk.AnisoF002.C03.IsotropicAwaySupportJets
import IsingBulk.AnisoF002.C03.IsotropicRetainedPowerControls

/-!
# A genuine positive diameter and scale on compact cutoff support

Smooth angular cutoffs whose closed support avoids constant tuples have
uniformly bounded finite jets and a positive actual diameter. Thus their
fixed-particle transport denominators remain uniformly bounded through
the radial limit, without any retained-pair condition.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set Metric
open scoped Topology BigOperators ContDiff

def angularPairSpread {N : ℕ} (θ : Fin N → ℝ) : ℝ :=
  ∑ i, ∑ l, (θ i - θ l) ^ 2

theorem angularPairSpread_continuous (N : ℕ) :
    Continuous (angularPairSpread : (Fin N → ℝ) → ℝ) := by
  unfold angularPairSpread
  fun_prop

theorem angularPairSpread_pos {N : ℕ} (θ : Fin N → ℝ) (hθ : ∃ i l, θ i ≠ θ l) :
    0 < angularPairSpread θ := by
  obtain ⟨i, l, hil⟩ := hθ
  apply (sq_pos_of_ne_zero (sub_ne_zero.mpr hil)).trans_le
  apply (Finset.single_le_sum (fun k _ => sq_nonneg (θ i - θ k)) (Finset.mem_univ l)).trans
  exact Finset.single_le_sum (fun k _ => Finset.sum_nonneg (fun t _ => sq_nonneg (θ k - θ t)))
    (Finset.mem_univ i)

theorem angularPairSpread_le_diameter {N : ℕ} (θ : Fin N → ℝ) {r : ℝ} (hr : 0 ≤ r)
    (hdiam : ∀ i l, |θ i - θ l| ≤ 2 * r) :
    angularPairSpread θ ≤ (N : ℝ) ^ 2 * (2 * r) ^ 2 := by
  calc
    _ ≤ ∑ _i : Fin N, ∑ _l : Fin N, (2 * r) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro l _
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr (hdiam i l)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

theorem rectangular_cutoff_hasCompactSupport {N : ℕ} {g : (Fin N → ℝ) → ℂ} {L U : ℝ}
    (hsupport : ∀ θ ∈ tsupport g, ∀ i, θ i ∈ Icc L U) : HasCompactSupport g := by
  apply isCompact_Icc.of_isClosed_subset isClosed_closure
    (s := Icc (fun _ : Fin N => L) (fun _ => U))
  intro θ ht
  exact ⟨fun i => (hsupport θ ht i).1, fun i => (hsupport θ ht i).2⟩

theorem rectangular_cutoff_finite_jet_control {N : ℕ} {g : (Fin N → ℝ) → ℂ} {L U : ℝ}
    (hg : ContDiff ℝ ∞ g) (hsupport : ∀ θ ∈ tsupport g, ∀ i, θ i ∈ Icc L U) (j : ℕ) :
    ∃ Cg : ℝ, 0 < Cg ∧ FiniteJetControl j g Cg := by
  obtain ⟨C, _, hC⟩ := (rectangular_cutoff_hasCompactSupport hsupport).exists_bound_iteratedFDeriv hg j
  exact ⟨max 1 C, zero_lt_one.trans_le (le_max_left _ _), hg.of_le (by simp),
    fun k hk θ => (hC k hk θ).trans (le_max_right _ _)⟩

theorem exists_rectangular_cutoff_diameter_gap {N : ℕ} (hN : 0 < N)
    {g : (Fin N → ℝ) → ℂ} {L U : ℝ}
    (hsupport : ∀ θ ∈ tsupport g, ∀ i, θ i ∈ Icc L U)
    (haway : ∀ θ ∈ tsupport g, ∃ i l, θ i ≠ θ l) :
    ∃ d : ℝ, 0 < d ∧ ∀ θ ∈ tsupport g, ∀ r : ℝ, 0 ≤ r →
      (∀ i l, |θ i - θ l| ≤ 2 * r) → d ≤ r := by
  have hK : IsCompact (tsupport g) := rectangular_cutoff_hasCompactSupport hsupport
  obtain ⟨q, hq, hqmin⟩ := hK.exists_forall_le' (angularPairSpread_continuous N).continuousOn
    (fun θ ht => angularPairSpread_pos θ (haway θ ht))
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  refine ⟨Real.sqrt q / (2 * N), by positivity, ?_⟩
  intro θ ht r hr hdiam
  have hsq := (hqmin θ ht).trans (angularPairSpread_le_diameter θ hr hdiam)
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * N)).mpr
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · nlinarith only [hsq]

theorem angularMean_abs_bound {N : ℕ} (hN : 0 < N) (u : Fin N → ℝ) (A : ℝ)
    (hu : ∀ i, |u i| ≤ A) : |angularMean u| ≤ A := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  rw [angularMean, abs_div, abs_of_pos hn]
  apply (div_le_iff₀ hn).mpr
  calc
    _ ≤ ∑ i, |u i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin N, A := Finset.sum_le_sum (fun i _ => hu i)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

theorem isotropicShellDelta_diameter_gap {N : ℕ} (hN : 0 < N)
    (b β ε r d : ℝ) (θ : Fin N → ℝ) (hb : 0 < b ∧ b < Real.pi) (hβ : β ≤ 1)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hr : 0 < r) (_hd : 0 ≤ d) (hdr : d ≤ r)
    (hθ : ∀ i, θ i ∈ Icc (-b - β) β) (hlow : ∃ i l, r ≤ |θ i - θ l|) :
    d / Real.sqrt (2 * Real.pi + 4) ≤ isotropicShellDelta b ε r θ := by
  have hm : |angularMean (fun i => θ i + b)| ≤ b + β := by
    apply angularMean_abs_bound hN
    intro i
    exact abs_le.mpr ⟨by linarith [(hθ i).1, hb.1], by linarith [(hθ i).2]⟩
  have hrmax : r ≤ Real.pi + 2 := by
    obtain ⟨i, l, hil⟩ := hlow
    have hdiff : |θ i - θ l| ≤ b + 2 * β := abs_le.mpr
      ⟨by linarith [(hθ i).1, (hθ l).2], by linarith [(hθ i).2, (hθ l).1]⟩
    linarith
  have hT : 0 < isotropicShellT b ε r θ := by unfold isotropicShellT; positivity
  have hTmax : isotropicShellT b ε r θ ≤ 2 * Real.pi + 4 := by
    unfold isotropicShellT
    linarith
  unfold isotropicShellDelta
  exact (div_le_div_of_nonneg_right hdr (Real.sqrt_nonneg _)).trans
    (div_le_div_of_nonneg_left hr.le (Real.sqrt_pos.mpr hT) (Real.sqrt_le_sqrt hTmax))

end
end IsingBulk.AnisoF002.Isotropic
