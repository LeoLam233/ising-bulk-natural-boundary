import IsingBulk.AnisoF002.C03.IsotropicPositiveDiameterGeometry
import IsingBulk.AnisoF002.C03.IsotropicCoareaBufferSignedShell
import IsingBulk.AnisoF002.C03.IsotropicCountableCoarea

/-!
# Complete coarea away from full coincidence, including small particles

The geometric angular buffer precedes the bump width. A positive fixed
diameter removes only the full coincidence. The genuine complete signed
physical density is bounded by a finite sum of its coarea shells for
every N >= 2; no positive collision exponent or large-N condition is
used. The constant is uniform in the angular mean and radial depth.
-/

noncomputable section
namespace IsingBulk.AnisoF002.Isotropic
open scoped Topology BigOperators
open Set Filter MeasureTheory

theorem positiveDiameter_integral_le_finite_shells {d K : ℕ}
    (ρ b β r₀ : ℝ) (hb : 0 < b) (hβ : 0 ≤ β) (hr₀ : 0 < r₀)
    (hK : dyadicRadius (b + 2 * β) K < r₀ / 2)
    (f : (Fin d → ℝ) → ℝ) (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x) :
    (∫ x in actualPositiveDiameterDomain d ρ b β r₀, f x) ≤
      ∑ k : Fin K, ∫ x in actualCenteredShell d ρ b β (dyadicRadius (b + 2 * β) k), f x := by
  let S := actualPositiveDiameterDomain d ρ b β r₀
  let T := fun k : Fin K => actualCenteredShell d ρ b β (dyadicRadius (b + 2 * β) k)
  have hS := actualPositiveDiameterDomain_isCompact d ρ b β r₀
  have hT (k : Fin K) := actualCenteredShell_isCompact d ρ b β (dyadicRadius (b + 2 * β) k)
  have hSI : Integrable (S.indicator f) volume :=
    (integrable_indicator_iff hS.measurableSet).mpr (hf.continuousOn.integrableOn_compact hS)
  have hTI (k) : Integrable ((T k).indicator f) volume :=
    (integrable_indicator_iff (hT k).measurableSet).mpr (hf.continuousOn.integrableOn_compact (hT k))
  have hnonneg (k) (x) : 0 ≤ (T k).indicator f x := indicator_nonneg (fun y _ => hf0 y) x
  have hpt (x : Fin d → ℝ) : S.indicator f x ≤ ∑ k, (T k).indicator f x := by
    by_cases hx : x ∈ S
    · have hu := actualPositiveDiameterDomain_subset_finite_shells ρ b β r₀ hb hβ hr₀ hK hx
      obtain ⟨k, hk⟩ := mem_iUnion.mp hu
      rw [indicator_of_mem hx]
      calc
        f x = (T k).indicator f x := (indicator_of_mem hk f).symm
        _ ≤ _ := Finset.single_le_sum (fun l _ => hnonneg l x) (Finset.mem_univ k)
    · rw [indicator_of_notMem hx]
      exact Finset.sum_nonneg (fun k _ => hnonneg k x)
  have hh := integral_mono hSI (integrable_finsetSum Finset.univ (fun k _ => hTI k)) hpt
  rw [integral_finsetSum Finset.univ (fun k _ => hTI k), integral_indicator hS.measurableSet] at hh
  have he (k : Fin K) : (∫ x, (T k).indicator f x) = ∫ x in T k, f x :=
    integral_indicator (hT k).measurableSet
  simp_rw [he] at hh
  exact hh

theorem positiveDiameter_shell_scalar_bound (n : ℕ) (C W A R q μ r ε : ℝ)
    (hC : 0 < C) (hW : 0 < W) (hA : 0 ≤ A) (hq : 0 < q)
    (hqr : q ≤ r) (hrR : r ≤ R) (hμ : |μ| ≤ A) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (C * (n + 2) ^ 3 * Real.sqrt (|μ| + r + ε) / r * (1 + |Real.log ε|)) *
        (24 * W * r / Real.sqrt (|μ| + r + ε)) ^ n ≤
      (C * (n + 2) ^ 3 * (Real.sqrt (A + R + 1) / q) *
        (24 * W * R / Real.sqrt q) ^ n) * (1 + |Real.log ε|) := by
  have hr : 0 < r := hq.trans_le hqr
  have hR : 0 < R := hr.trans_le hrR
  have hsq : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq
  have hst : 0 < Real.sqrt (|μ| + r + ε) := Real.sqrt_pos.mpr (by positivity)
  have hlow : Real.sqrt q ≤ Real.sqrt (|μ| + r + ε) :=
    Real.sqrt_le_sqrt (by linarith only [hqr, abs_nonneg μ, hε])
  have hupp : Real.sqrt (|μ| + r + ε) ≤ Real.sqrt (A + R + 1) :=
    Real.sqrt_le_sqrt (by linarith only [hμ, hrR, hε1])
  have hfrac : Real.sqrt (|μ| + r + ε) / r ≤ Real.sqrt (A + R + 1) / q :=
    (div_le_div_of_nonneg_right hupp hr.le).trans
      (div_le_div_of_nonneg_left (Real.sqrt_nonneg _) hq hqr)
  have hbase : 24 * W * r / Real.sqrt (|μ| + r + ε) ≤ 24 * W * R / Real.sqrt q :=
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hrR (by positivity)) hst.le).trans
      (div_le_div_of_nonneg_left (by positivity) hsq hlow)
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ 24 * W * r / Real.sqrt (|μ| + r + ε)) hbase n
  calc
    _ = (C * (n + 2) ^ 3 * (Real.sqrt (|μ| + r + ε) / r)) *
        (24 * W * r / Real.sqrt (|μ| + r + ε)) ^ n * (1 + |Real.log ε|) := by ring
    _ ≤ (C * (n + 2) ^ 3 * (Real.sqrt (A + R + 1) / q)) *
        (24 * W * R / Real.sqrt q) ^ n * (1 + |Real.log ε|) := by gcongr
    _ = _ := by ring

theorem exists_actual_positive_diameter_coarea_buffer (α b : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α) :
    ∃ β : ℝ, 0 < β ∧ β ≤ 1 ∧ ∀ η : ℝ, 0 < η → 4 * η ≤ Real.sin b →
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ β ∧ ∀ (n : ℕ) (r₀ : ℝ), 0 < r₀ →
        ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, 0 < ε → ε ≤ δ →
        ∀ τ ξ : ℝ, τ ∈ Icc 0 δ → ξ ∈ Icc 0 1 → ∀ μ : ℝ,
        ∀ σ : ℂ, σ = 1 ∨ σ = -1 →
          (∫ x in actualPositiveDiameterDomain (n + 1) (μ - b) b β r₀,
            actualSignedFullDensity (isotropicRadialParameter α ε) σ η τ ξ
              (centeredConstraintAngles (μ - b) x)) ≤ K * (1 + |Real.log ε|) := by
  obtain ⟨β, hβ, hβ1, hdata⟩ := exists_actual_complete_signed_shell_coarea_buffer α b hα hb hpoint
  refine ⟨β, hβ, hβ1, ?_⟩
  intro η hη hwidth
  obtain ⟨δ, C, W, hδ, hδβ, hC, hW, hbound⟩ := hdata η hη hwidth
  refine ⟨δ, hδ, hδβ, ?_⟩
  intro n r₀ hr₀
  have hb0 := hb.1
  let R := b + 2 * β
  have hR : 0 < R := by dsimp [R]; positivity
  obtain ⟨k₀, hk₀⟩ := exists_dyadicRadius_below hR hr₀
  let q := dyadicRadius R k₀
  have hq : 0 < q := dyadicRadius_pos R hR k₀
  let B := C * (n + 2) ^ 3 * (Real.sqrt (b + β + R + 1) / q) *
    (24 * W * R / Real.sqrt q) ^ n
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨1 + k₀ * B, by positivity, ?_⟩
  intro ε hε hεδ τ ξ hτ hξ μ σ hσ
  let s := isotropicRadialParameter α ε
  let f := fun x : Fin (n + 1) → ℝ => actualSignedFullDensity s σ η τ ξ
    (centeredConstraintAngles (μ - b) x)
  have hε1 : ε ≤ 1 := hεδ.trans (hδβ.trans hβ1)
  have hs : 0 < s.im := (isotropicRadialParameter_estimates α ε hα hε hε1).2.2.2.1
  have hf : Continuous f := (actualSignedFullDensity_continuous (by omega) s σ hs hσ η τ ξ
    hη hτ.1 hξ.1).comp (centeredConstraintAngles_continuous (μ - b))
  by_cases hne : (actualCenteredRightDomain (n + 1) (μ - b) b β).Nonempty
  · have hμ := actualCenteredRightDomain_mean_bound hb.1.le hne
    have hshell (k : Fin k₀) :
        (∫ x in actualCenteredShell (n + 1) (μ - b) b β (dyadicRadius R k), f x) ≤
          B * (1 + |Real.log ε|) := by
      have hkr : q ≤ dyadicRadius R k := dyadicRadius_antitone R hR.le (Nat.le_of_lt k.isLt)
      have hkR : dyadicRadius R k ≤ R := by
        simpa only [dyadicRadius_zero] using dyadicRadius_antitone R hR.le (Nat.zero_le (k : ℕ))
      exact (hbound n ε hε hεδ τ ξ hτ hξ μ _ (dyadicRadius_pos R hR k) σ hσ).trans
        (positiveDiameter_shell_scalar_bound n C W (b + β) R q μ _ ε hC hW
          (by positivity) hq hkr hkR hμ hε hε1)
    have hh := (positiveDiameter_integral_le_finite_shells (μ - b) b β r₀ hb.1 hβ.le hr₀ hk₀ f hf
      (fun x => actualSignedFullDensity_nonneg _ _ _ _ _ _)).trans
      (Finset.sum_le_sum (fun k _ => hshell k))
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hh
    exact hh.trans (by nlinarith [abs_nonneg (Real.log ε)])
  · have he : actualPositiveDiameterDomain (n + 1) (μ - b) b β r₀ = ∅ := by
      apply not_nonempty_iff_eq_empty.mp
      rintro ⟨x, hx⟩
      exact hne ⟨x, hx.1⟩
    rw [he, Measure.restrict_empty, integral_zero_measure]
    positivity

end IsingBulk.AnisoF002.Isotropic
