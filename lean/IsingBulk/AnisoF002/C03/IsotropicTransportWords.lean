import IsingBulk.AnisoF002.C03.IsotropicSeparatedTransport

/-!
# Finite separated words for the full transport recurrence

A word records either analytic covariance transport or one exact real
cutoff derivative. Its analytic and angular factors remain separate.
Every branch is retained, with an explicit finite population count.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators ContDiff

abbrev TransportBranch (N : ℕ) := Option (Fin N × Fin N)
abbrev TransportWord (N n : ℕ) := Fin n → TransportBranch N

def transportWordConsEquiv (N n : ℕ) :
    TransportWord N (n + 1) ≃ TransportBranch N × TransportWord N n where
  toFun w := (w 0, fun i => w i.succ)
  invFun w := Fin.cons w.1 w.2
  left_inv w := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  right_inv w := by
    apply Prod.ext
    · rfl
    · rfl

theorem transportWord_sum_succ {A : Type*} [AddCommMonoid A] (N n : ℕ)
    (f : TransportWord N (n + 1) → A) :
    (∑ w, f w) = ∑ b : TransportBranch N, ∑ w : TransportWord N n, f (Fin.cons b w) := by
  calc
    _ = ∑ u : TransportBranch N × TransportWord N n, f (Fin.cons u.1 u.2) :=
      ((transportWordConsEquiv N n).symm.sum_comp f).symm
    _ = _ := Fintype.sum_prod_type _

theorem transportWord_card (N n : ℕ) : Fintype.card (TransportWord N n) = (1 + N ^ 2) ^ n := by
  simp only [TransportWord, TransportBranch, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_option, Fintype.card_prod]
  congr 1
  ring

noncomputable def transportAnalyticWord {N : ℕ}
    (B K : RegularJointSpace N → Fin N → ℂ) (F : RegularJointSpace N → ℂ) :
    (n : ℕ) → TransportWord N n → RegularJointSpace N → ℂ
  | 0, _ => F
  | n + 1, w =>
    match w 0 with
    | none => analyticTransportAmplitude B (transportAnalyticWord B K F n (fun i => w i.succ))
    | some ij => fun p => transportAnalyticWord B K F n (fun i => w i.succ) p * K p ij.2

noncomputable def transportAngularWord {N : ℕ}
    (A : Fin N → Fin N → (Fin N → ℝ) → ℂ) (g : (Fin N → ℝ) → ℂ) :
    (n : ℕ) → TransportWord N n → (Fin N → ℝ) → ℂ
  | 0, _ => g
  | n + 1, w =>
    match w 0 with
    | none => transportAngularWord A g n (fun i => w i.succ)
    | some ij => fun θ => A ij.1 ij.2 θ *
        realAngularPartial (transportAngularWord A g n (fun i => w i.succ)) ij.1 θ

theorem transportAnalyticWord_analyticAt {N : ℕ}
    (B K : RegularJointSpace N → Fin N → ℂ) (F : RegularJointSpace N → ℂ)
    (p : RegularJointSpace N) (hB : AnalyticAt ℂ B p)
    (hK : ∀ j, AnalyticAt ℂ (fun q => K q j) p) (hF : AnalyticAt ℂ F p)
    (n : ℕ) (w : TransportWord N n) : AnalyticAt ℂ (transportAnalyticWord B K F n w) p := by
  induction n with
  | zero => exact hF
  | succ n ih =>
    simp only [transportAnalyticWord]
    cases hw : w 0 with
    | none => exact analyticTransportAmplitude_analyticAt B _ p hB (ih _)
    | some ij => exact (ih _).mul (hK ij.2)

theorem transportAngularWord_contDiffAt {N : ℕ}
    (A : Fin N → Fin N → (Fin N → ℝ) → ℂ) (g : (Fin N → ℝ) → ℂ)
    (θ : Fin N → ℝ) (hA : ∀ i j, ContDiffAt ℝ ∞ (A i j) θ)
    (hg : ContDiffAt ℝ ∞ g θ) (n : ℕ) (w : TransportWord N n) :
    ContDiffAt ℝ ∞ (transportAngularWord A g n w) θ := by
  induction n with
  | zero => exact hg
  | succ n ih =>
    simp only [transportAngularWord]
    cases hw : w 0 with
    | none => exact ih _
    | some ij =>
      exact (hA ij.1 ij.2).mul (scalarPartial_contDiffAt _ _ θ (ih _))

theorem transportAngularWord_finite_jet_bound {N k : ℕ}
    (A : Fin N → Fin N → (Fin N → ℝ) → ℂ) (g : (Fin N → ℝ) → ℂ)
    (CA Cg : ℝ) (hCA : 1 ≤ CA) (hCg : 0 ≤ Cg)
    (hA : ∀ i j, FiniteJetControl k (A i j) CA) (hg : FiniteJetControl k g Cg)
    (n : ℕ) (hn : n ≤ k) (w : TransportWord N n) :
    FiniteJetControl (k - n) (transportAngularWord A g n w)
      ((2 ^ k * CA) ^ n * Cg) := by
  have hstep : 1 ≤ (2 : ℝ) ^ k * CA :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) hCA
  induction n with
  | zero => simpa only [transportAngularWord, Nat.sub_zero, pow_zero, one_mul] using hg
  | succ n ih =>
    have hnk : n ≤ k := by omega
    have hbudget : k - n = (k - (n + 1)) + 1 := by omega
    have hprev := ih hnk (fun i => w i.succ)
    have hprevC : 0 ≤ (2 ^ k * CA) ^ n * Cg := by positivity
    have hlarge : (2 ^ k * CA) ^ n * Cg ≤ (2 ^ k * CA) ^ (n + 1) * Cg :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hstep (Nat.le_succ n)) hCg
    simp only [transportAngularWord]
    cases hw : w 0 with
    | none => exact (hprev.mono_order (by omega)).mono_bound hlarge
    | some ij =>
      rw [hbudget] at hprev
      have hD := realAngularPartial_jet_control _ ij.1 _ hprev
      have hAA := (hA ij.1 ij.2).mono_order (show k - (n + 1) ≤ k from Nat.sub_le _ _)
      apply (hAA.mul hD (zero_le_one.trans hCA) hprevC).mono_bound
      calc
        _ ≤ 2 ^ k * CA * ((2 ^ k * CA) ^ n * Cg) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.sub_le _ _))
              (zero_le_one.trans hCA)) hprevC
        _ = _ := by rw [pow_succ]; ring

end IsingBulk.AnisoF002.Isotropic
