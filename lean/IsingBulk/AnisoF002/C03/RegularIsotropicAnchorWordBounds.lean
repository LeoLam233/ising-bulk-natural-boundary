import IsingBulk.AnisoF002.C03.RegularIsotropicCoordinateWords
import IsingBulk.AnisoF002.C03.IsotropicTransportWordBounds

/-!
# Complete anchored word estimates

The protected radius is rho/N and both regular coefficients are O(N).
Every analytic transport branch therefore costs O(N^3). The exact real
inverse-entry and cutoff jets, and all (1+N^2)^j branches, are retained.
-/

noncomputable section
namespace IsingBulk.AnisoF002.Isotropic
open scoped Topology BigOperators
open Set Metric

def anchorWordCost (j : ℕ) (ρ L CA G : ℝ) : ℝ :=
  2 ^ j * transportBallConstant j * (((1 + 2 * L) / ρ + L) ^ j) *
    ((2 ^ j * CA) ^ j) * G

theorem anchorWordCost_pos (j : ℕ) {ρ L CA G : ℝ}
    (hρ : 0 < ρ) (hL : 0 < L) (hCA : 0 < CA) (hG : 0 < G) :
    0 < anchorWordCost j ρ L CA G := by
  unfold anchorWordCost
  have ht := transportBallConstant_pos j
  positivity

theorem anchored_transport_scale_bound {N : ℕ} (hN : 0 < N)
    {ρ L : ℝ} (hρ : 0 < ρ) (hL : 0 ≤ L) :
    (1 + 2 * (N : ℝ) * (L * N)) / (ρ / N) + L * N ≤
      ((1 + 2 * L) / ρ + L) * (N : ℝ) ^ 3 := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN3 : (N : ℝ) ≤ (N : ℝ) ^ 3 := by
    simpa only [pow_one] using pow_le_pow_right₀ hN1 (show 1 ≤ 3 by norm_num)
  calc
    _ = ((N : ℝ) + 2 * L * (N : ℝ) ^ 3) / ρ + L * N := by field_simp
    _ ≤ ((N : ℝ) ^ 3 + 2 * L * (N : ℝ) ^ 3) / ρ + L * (N : ℝ) ^ 3 :=
      add_le_add (div_le_div_of_nonneg_right (add_le_add hN3 le_rfl) hρ.le)
        (mul_le_mul_of_nonneg_left hN3 hL)
    _ = _ := by ring

theorem transportAnalyticWord_anchor_bound {N : ℕ} (hN : 0 < N)
    (B K : RegularJointSpace N → Fin N → ℂ) (F : RegularJointSpace N → ℂ)
    (q : RegularJointSpace N) (ρ L M : ℝ) (hρ : 0 < ρ) (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hB : AnalyticOnNhd ℂ B (ball q (ρ / N)))
    (hK : ∀ i, AnalyticOnNhd ℂ (fun p => K p i) (ball q (ρ / N)))
    (hF : AnalyticOnNhd ℂ F (ball q (ρ / N)))
    (hBL : ∀ p ∈ ball q (ρ / N), ‖B p‖ ≤ L * N)
    (hKL : ∀ p ∈ ball q (ρ / N), ∀ i, ‖K p i‖ ≤ L * N)
    (hFM : ∀ p ∈ ball q (ρ / N), ‖F p‖ ≤ M)
    (j : ℕ) (w : TransportWord N j) :
    ‖transportAnalyticWord B K F j w q‖ ≤
      transportBallConstant j * (((1 + 2 * L) / ρ + L) ^ j) *
        (N : ℝ) ^ (3 * j) * M := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hh := transportAnalyticWord_ball_bound B K F q (ρ / N) (L * N) (L * N) M
    (by positivity) (by positivity) (by positivity) hM hB hK hF hBL hKL hFM j w q
    (mem_ball_self (by positivity))
  have hs := anchored_transport_scale_bound hN hρ hL
  have hp := pow_le_pow_left₀ (by positivity) hs j
  exact hh.trans ((mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hp (transportBallConstant_pos j).le) hM).trans_eq (by
      simp only [mul_pow, ← pow_mul]
      ring))

theorem transportWord_card_real_bound {N : ℕ} (hN : 0 < N) (j : ℕ) :
    (Fintype.card (TransportWord N j) : ℝ) ≤ 2 ^ j * (N : ℝ) ^ (2 * j) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN2 : (1 : ℝ) ≤ (N : ℝ) ^ 2 := one_le_pow₀ hN1
  rw [transportWord_card]
  simp only [Nat.cast_pow, Nat.cast_add, Nat.cast_one]
  have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1 + (N : ℝ) ^ 2)
    (show 1 + (N : ℝ) ^ 2 ≤ 2 * (N : ℝ) ^ 2 by linarith only [hN2]) j
  simpa only [mul_pow, ← pow_mul] using hp

theorem coordinateSeparatedWordSum_anchor_bound {N : ℕ} (hN : 0 < N)
    (B K : RegularJointSpace N → Fin N → ℂ) (F : RegularJointSpace N → ℂ)
    (η τ ξ : ℝ) (g : (Fin N → ℝ) → ℂ) (x : ℂ × (Fin N → ℝ))
    (ρ L M CA G D : ℝ) (j m : ℕ)
    (hρ : 0 < ρ) (hL : 0 ≤ L) (hM : 0 ≤ M) (hCA : 1 ≤ CA) (hG : 0 ≤ G) (hD : 0 ≤ D)
    (hB : AnalyticOnNhd ℂ B (ball (regularJointMap (actualPhysicalCoordinate η τ ξ) x) (ρ / N)))
    (hK : ∀ i, AnalyticOnNhd ℂ (fun p => K p i)
      (ball (regularJointMap (actualPhysicalCoordinate η τ ξ) x) (ρ / N)))
    (hF : AnalyticOnNhd ℂ F (ball (regularJointMap (actualPhysicalCoordinate η τ ξ) x) (ρ / N)))
    (hBL : ∀ p ∈ ball (regularJointMap (actualPhysicalCoordinate η τ ξ) x) (ρ / N), ‖B p‖ ≤ L * N)
    (hKL : ∀ p ∈ ball (regularJointMap (actualPhysicalCoordinate η τ ξ) x) (ρ / N), ∀ i, ‖K p i‖ ≤ L * N)
    (hFM : ∀ p ∈ ball (regularJointMap (actualPhysicalCoordinate η τ ξ) x) (ρ / N), ‖F p‖ ≤ M)
    (hA : ∀ i l : Fin N, FiniteJetControl j (actualBalancedInverseEntry η τ ξ i l)
      (CA * (N : ℝ) ^ (3 * j)))
    (hg : FiniteJetControl j g (G * D ^ N * (N : ℝ) ^ m)) :
    ‖coordinateSeparatedWordSum B K η τ ξ F g j x‖ ≤
      anchorWordCost j ρ L CA G * D ^ N *
        (N : ℝ) ^ (2 * j + 3 * j + 3 * j * j + m) * M := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hCA0 := zero_le_one.trans hCA
  have hAL : 1 ≤ CA * (N : ℝ) ^ (3 * j) :=
    one_le_mul_of_one_le_of_one_le hCA (one_le_pow₀ hN1)
  let P := transportBallConstant j * (((1 + 2 * L) / ρ + L) ^ j) * (N : ℝ) ^ (3 * j) * M
  let Q := ((2 ^ j * (CA * (N : ℝ) ^ (3 * j))) ^ j) * (G * D ^ N * (N : ℝ) ^ m)
  have hP : 0 ≤ P := by dsimp [P]; exact mul_nonneg (mul_nonneg
    (mul_nonneg (transportBallConstant_pos j).le (by positivity)) (by positivity)) hM
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hword (w : TransportWord N j) :
      ‖transportAnalyticWord B K F j w (regularJointMap (actualPhysicalCoordinate η τ ξ) x) *
        transportAngularWord (actualBalancedInverseEntry η τ ξ) g j w x.2‖ ≤ P * Q := by
    have hf := transportAnalyticWord_anchor_bound hN B K F _ ρ L M hρ hL hM hB hK hF hBL hKL hFM j w
    have hg0 := (transportAngularWord_finite_jet_bound
      (actualBalancedInverseEntry η τ ξ) g (CA * (N : ℝ) ^ (3 * j))
      (G * D ^ N * (N : ℝ) ^ m) hAL (by positivity) hA hg j le_rfl w).bound 0 (by omega) x.2
    rw [norm_iteratedFDeriv_zero] at hg0
    rw [norm_mul]
    exact mul_le_mul hf hg0 (norm_nonneg _) hP
  calc
    _ ≤ ∑ w : TransportWord N j, ‖transportAnalyticWord B K F j w
        (regularJointMap (actualPhysicalCoordinate η τ ξ) x) *
        transportAngularWord (actualBalancedInverseEntry η τ ξ) g j w x.2‖ := norm_sum_le _ _
    _ ≤ ∑ _w : TransportWord N j, P * Q := Finset.sum_le_sum (fun w _ => hword w)
    _ = (Fintype.card (TransportWord N j) : ℝ) * (P * Q) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ (2 ^ j * (N : ℝ) ^ (2 * j)) * (P * Q) :=
      mul_le_mul_of_nonneg_right (transportWord_card_real_bound hN j) (mul_nonneg hP hQ)
    _ = _ := by
      dsimp [P, Q, anchorWordCost]
      simp only [mul_pow, ← pow_mul, pow_add]
      ring

end IsingBulk.AnisoF002.Isotropic
