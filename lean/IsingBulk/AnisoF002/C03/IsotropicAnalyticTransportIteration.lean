import IsingBulk.AnisoF002.C03.IsotropicAnalyticTransport

/-!
# All complete analytic transport descendants on the same protected ball

The recurrence differentiates every prior amplitude and every coefficient.
The radius loss depends only on the number of applications, and the full
divergence is present at every stage. These are analytic numerator bounds;
smooth angular cutoffs are treated separately by the real-frame product rule.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators
open Set Metric

noncomputable def analyticTransportDescendant {N : ℕ}
    (B : RegularJointSpace N → Fin N → ℂ) (b : RegularJointSpace N → ℂ) :
    ℕ → RegularJointSpace N → ℂ
  | 0 => b
  | n + 1 => analyticTransportAmplitude B (analyticTransportDescendant B b n)

noncomputable def transportBallConstant : ℕ → ℝ
  | 0 => 1
  | n + 1 => 8 * 2 ^ n * transportBallConstant n

theorem transportBallConstant_pos (n : ℕ) : 0 < transportBallConstant n := by
  induction n with
  | zero => exact zero_lt_one
  | succ n ih => change 0 < 8 * 2 ^ n * transportBallConstant n; positivity

theorem analyticTransportDescendant_analyticAt {N : ℕ}
    (B : RegularJointSpace N → Fin N → ℂ) (b : RegularJointSpace N → ℂ)
    (q : RegularJointSpace N) (hB : AnalyticAt ℂ B q) (hb : AnalyticAt ℂ b q)
    (n : ℕ) : AnalyticAt ℂ (analyticTransportDescendant B b n) q := by
  induction n with
  | zero => exact hb
  | succ n ih => exact analyticTransportAmplitude_analyticAt B _ q hB ih

/-- A single bound on a common ball controls the full transport recurrence
at every order, with an explicit fixed-order radius loss. -/
theorem analyticTransportDescendant_ball_bound {N : ℕ}
    (B : RegularJointSpace N → Fin N → ℂ) (b : RegularJointSpace N → ℂ)
    (q : RegularJointSpace N) (r L M : ℝ) (hr : 0 < r) (hL : 0 ≤ L)
    (hB : AnalyticOnNhd ℂ B (ball q r)) (hb : AnalyticOnNhd ℂ b (ball q r))
    (hBL : ∀ p ∈ ball q r, ‖B p‖ ≤ L) (hbM : ∀ p ∈ ball q r, ‖b p‖ ≤ M)
    (n : ℕ) (p : RegularJointSpace N) (hp : p ∈ ball q (r / 2 ^ n)) :
    ‖analyticTransportDescendant B b n p‖ ≤
      transportBallConstant n * (1 + 2 * (N : ℝ) * L) ^ n / r ^ n * M := by
  induction n generalizing p with
  | zero => simpa only [analyticTransportDescendant, transportBallConstant, pow_zero,
      div_one, mul_one, one_mul] using hbM p (by simpa using hp)
  | succ n ih =>
    have hrn : 0 < r / 2 ^ n := by positivity
    have hsub : ball q (r / 2 ^ n) ⊆ ball q r :=
      ball_subset_ball (div_le_self hr.le (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)))
    have hbd : AnalyticOnNhd ℂ (analyticTransportDescendant B b n) (ball q (r / 2 ^ n)) := by
      intro z hz
      exact analyticTransportDescendant_analyticAt B b z (hB z (hsub hz)) (hb z (hsub hz)) n
    have hphalf : p ∈ ball q ((r / 2 ^ n) / 2) := by
      simpa only [pow_succ, div_mul_eq_div_div] using hp
    have hh := analyticTransportAmplitude_ball_bound B (analyticTransportDescendant B b n)
      q (r / 2 ^ n) L
      (transportBallConstant n * (1 + 2 * (N : ℝ) * L) ^ n / r ^ n * M)
      hrn hL (hB.mono hsub) hbd (fun z hz => hBL z (hsub hz))
      (fun z hz => ih z hz) p hphalf
    change ‖analyticTransportAmplitude B (analyticTransportDescendant B b n) p‖ ≤ _
    exact hh.trans_eq (by
      simp only [transportBallConstant, pow_succ]
      field_simp)

/-- Every joint derivative of the complete descendant is taken after the
entire recurrence. In particular this includes all parameter derivatives
of the covariance field and all previous descendants. -/
theorem analyticTransportDescendant_joint_jet_bound {N : ℕ}
    (B : RegularJointSpace N → Fin N → ℂ) (b : RegularJointSpace N → ℂ)
    (q : RegularJointSpace N) (r L M : ℝ) (hr : 0 < r) (hL : 0 ≤ L)
    (hB : AnalyticOnNhd ℂ B (ball q r)) (hb : AnalyticOnNhd ℂ b (ball q r))
    (hBL : ∀ p ∈ ball q r, ‖B p‖ ≤ L) (hbM : ∀ p ∈ ball q r, ‖b p‖ ≤ M)
    (n k : ℕ) :
    ‖iteratedFDeriv ℂ k (analyticTransportDescendant B b n) q‖ ≤
      protectedJetConstant k (r / 2 ^ n) *
        (transportBallConstant n * (1 + 2 * (N : ℝ) * L) ^ n / r ^ n * M) := by
  have hsub : ball q (r / 2 ^ n) ⊆ ball q r :=
    ball_subset_ball (div_le_self hr.le (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)))
  apply analytic_ball_joint_jet_bound k _ q (r / 2 ^ n) _ (by positivity)
  · intro p hp
    exact analyticTransportDescendant_analyticAt B b p (hB p (hsub hp)) (hb p (hsub hp)) n
  · intro p hp
    exact analyticTransportDescendant_ball_bound B b q r L M hr hL hB hb hBL hbM n p hp

end IsingBulk.AnisoF002.Isotropic
