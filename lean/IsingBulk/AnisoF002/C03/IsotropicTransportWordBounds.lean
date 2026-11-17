import IsingBulk.AnisoF002.C03.IsotropicTransportWords

/-!
# Uniform bounds for every separated analytic word

The estimate treats every cutoff branch and every covariance-derivative
branch on one protected ball. All subsequent Cauchy derivatives act on
the whole preceding word, including its parameter-dependent factors.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators
open Set Metric

theorem transportAnalyticWord_ball_bound {N : ℕ}
    (B K : RegularJointSpace N → Fin N → ℂ) (F : RegularJointSpace N → ℂ)
    (q : RegularJointSpace N) (r L H M : ℝ) (hr : 0 < r)
    (hL : 0 ≤ L) (hH : 0 ≤ H) (hM : 0 ≤ M)
    (hB : AnalyticOnNhd ℂ B (ball q r))
    (hK : ∀ j, AnalyticOnNhd ℂ (fun p => K p j) (ball q r))
    (hF : AnalyticOnNhd ℂ F (ball q r))
    (hBL : ∀ p ∈ ball q r, ‖B p‖ ≤ L)
    (hKH : ∀ p ∈ ball q r, ∀ j, ‖K p j‖ ≤ H)
    (hFM : ∀ p ∈ ball q r, ‖F p‖ ≤ M)
    (n : ℕ) (w : TransportWord N n) (p : RegularJointSpace N)
    (hp : p ∈ ball q (r / 2 ^ n)) :
    ‖transportAnalyticWord B K F n w p‖ ≤
      transportBallConstant n * ((1 + 2 * (N : ℝ) * L) / r + H) ^ n * M := by
  let A := (1 + 2 * (N : ℝ) * L) / r + H
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hHle : H ≤ A := le_add_of_nonneg_left (by positivity)
  have hAr : 1 + 2 * (N : ℝ) * L ≤ A * r := by
    dsimp [A]
    rw [add_mul, div_mul_cancel₀ _ hr.ne']
    exact le_add_of_nonneg_right (mul_nonneg hH hr.le)
  induction n generalizing p with
  | zero => simpa only [transportAnalyticWord, transportBallConstant, pow_zero, div_one,
      mul_one, one_mul] using hFM p (by simpa using hp)
  | succ n ih =>
    have hrn : 0 < r / 2 ^ n := by positivity
    have hsub : ball q (r / 2 ^ n) ⊆ ball q r :=
      ball_subset_ball (div_le_self hr.le (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)))
    have hphalf : p ∈ ball q ((r / 2 ^ n) / 2) := by
      simpa only [pow_succ, div_mul_eq_div_div] using hp
    have hpold : p ∈ ball q (r / 2 ^ n) :=
      ball_subset_ball (half_le_self hrn.le) hphalf
    have hbound0 : 0 ≤ transportBallConstant n * A ^ n * M :=
      mul_nonneg (mul_nonneg (transportBallConstant_pos n).le (pow_nonneg hA n)) hM
    have hword : AnalyticOnNhd ℂ
        (transportAnalyticWord B K F n (fun i => w i.succ)) (ball q (r / 2 ^ n)) := by
      intro z hz
      exact transportAnalyticWord_analyticAt B K F z (hB z (hsub hz))
        (fun j => hK j z (hsub hz)) (hF z (hsub hz)) n _
    change ‖transportAnalyticWord B K F (n + 1) w p‖ ≤ transportBallConstant (n + 1) * A ^ (n + 1) * M
    simp only [transportAnalyticWord]
    cases hw : w 0 with
    | none =>
      have hh := analyticTransportAmplitude_ball_bound B
        (transportAnalyticWord B K F n (fun i => w i.succ)) q (r / 2 ^ n) L
        (transportBallConstant n * A ^ n * M) hrn hL (hB.mono hsub) hword
        (fun z hz => hBL z (hsub hz)) (fun z hz => ih _ z hz) p hphalf
      have hcost : 8 / (r / 2 ^ n) * (1 + 2 * (N : ℝ) * L) ≤ 8 * 2 ^ n * A := by
        calc
          _ ≤ 8 / (r / 2 ^ n) * (A * r) :=
            mul_le_mul_of_nonneg_left hAr (by positivity)
          _ = _ := by field_simp
      exact hh.trans ((mul_le_mul_of_nonneg_right hcost hbound0).trans_eq (by
        rw [transportBallConstant, pow_succ]
        ring))
    | some ij =>
      change ‖transportAnalyticWord B K F n (fun i => w i.succ) p * K p ij.2‖ ≤ _
      rw [norm_mul]
      have he : ‖transportAnalyticWord B K F n (fun i => w i.succ) p‖ * ‖K p ij.2‖ ≤
          (transportBallConstant n * A ^ n * M) * A :=
        mul_le_mul (ih _ p hpold) ((hKH p (hsub hpold) ij.2).trans hHle) (norm_nonneg _) hbound0
      have h8 : (1 : ℝ) ≤ 8 * 2 ^ n := by
        have hh : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
        linarith only [hh]
      have hlarge := le_mul_of_one_le_left (mul_nonneg hbound0 hA) h8
      exact he.trans (hlarge.trans_eq (by rw [transportBallConstant, pow_succ]; ring))

theorem transportAnalyticWord_joint_jet_bound {N : ℕ}
    (B K : RegularJointSpace N → Fin N → ℂ) (F : RegularJointSpace N → ℂ)
    (q : RegularJointSpace N) (r L H M : ℝ) (hr : 0 < r)
    (hL : 0 ≤ L) (hH : 0 ≤ H) (hM : 0 ≤ M)
    (hB : AnalyticOnNhd ℂ B (ball q r))
    (hK : ∀ j, AnalyticOnNhd ℂ (fun p => K p j) (ball q r))
    (hF : AnalyticOnNhd ℂ F (ball q r))
    (hBL : ∀ p ∈ ball q r, ‖B p‖ ≤ L)
    (hKH : ∀ p ∈ ball q r, ∀ j, ‖K p j‖ ≤ H)
    (hFM : ∀ p ∈ ball q r, ‖F p‖ ≤ M)
    (n k : ℕ) (w : TransportWord N n) :
    ‖iteratedFDeriv ℂ k (transportAnalyticWord B K F n w) q‖ ≤
      protectedJetConstant k (r / 2 ^ n) *
        (transportBallConstant n * ((1 + 2 * (N : ℝ) * L) / r + H) ^ n * M) := by
  have hsub : ball q (r / 2 ^ n) ⊆ ball q r :=
    ball_subset_ball (div_le_self hr.le (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)))
  apply analytic_ball_joint_jet_bound k _ q (r / 2 ^ n) _ (by positivity)
  · intro p hp
    exact transportAnalyticWord_analyticAt B K F p (hB p (hsub hp))
      (fun j => hK j p (hsub hp)) (hF p (hsub hp)) n w
  · intro p hp
    exact transportAnalyticWord_ball_bound B K F q r L H M hr hL hH hM hB hK hF hBL hKH hFM n w p hp

end IsingBulk.AnisoF002.Isotropic
