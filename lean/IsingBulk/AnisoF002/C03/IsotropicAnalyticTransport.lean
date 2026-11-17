import IsingBulk.AnisoF002.C03.IsotropicInitialCollisionJets

/-!
# Quantitative complete analytic transport in the regular coordinates

This is the full first-order operator, including the divergence of the
parameter-dependent field. Bounds come from genuine common complex
balls. No coefficient or previous descendant is held constant during
iteration.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators
open Set Metric

abbrev RegularJointSpace (N : ℕ) := ℂ × (Fin N → ℂ)

def regularComplexTimeDirection (N : ℕ) : RegularJointSpace N := (1, 0)

def regularComplexAngularDirection {N : ℕ} (i : Fin N) : RegularJointSpace N := (0, Pi.single i 1)

def analyticTransportAmplitude {N : ℕ} (B : RegularJointSpace N → Fin N → ℂ)
    (b : RegularJointSpace N → ℂ) (q : RegularJointSpace N) : ℂ :=
  fderiv ℂ b q (regularComplexTimeDirection N) +
    (∑ i, B q i * fderiv ℂ b q (regularComplexAngularDirection i)) +
    (∑ i, fderiv ℂ B q (regularComplexAngularDirection i) i) * b q

theorem analyticTransportAmplitude_analyticAt {N : ℕ}
    (B : RegularJointSpace N → Fin N → ℂ) (b : RegularJointSpace N → ℂ)
    (q : RegularJointSpace N) (hB : AnalyticAt ℂ B q) (hb : AnalyticAt ℂ b q) :
    AnalyticAt ℂ (analyticTransportAmplitude B b) q := by
  have hd (v : RegularJointSpace N) : AnalyticAt ℂ (fun p => fderiv ℂ b p v) q :=
    ((ContinuousLinearMap.apply ℂ ℂ v).analyticAt _).comp hb.fderiv
  have hDB (v : RegularJointSpace N) : AnalyticAt ℂ (fun p => fderiv ℂ B p v) q :=
    ((ContinuousLinearMap.apply ℂ (Fin N → ℂ) v).analyticAt _).comp hB.fderiv
  have hBi (i : Fin N) : AnalyticAt ℂ (fun p => B p i) q :=
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) i).analyticAt _).comp
      (f := B) hB
  have hdiag (i : Fin N) : AnalyticAt ℂ
      (fun p => fderiv ℂ B p (regularComplexAngularDirection i) i) q :=
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) i).analyticAt _).comp
      (f := fun p => fderiv ℂ B p (regularComplexAngularDirection i)) (hDB _)
  exact ((hd _).add (Finset.analyticAt_fun_sum _ (fun i _ => (hBi i).mul (hd _)))).add
    ((Finset.analyticAt_fun_sum _ (fun i _ => hdiag i)).mul hb)

theorem analytic_ball_inner_fderiv_bound
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (f : E → F) (q : E) (r M : ℝ) (hr : 0 < r)
    (hf : AnalyticOnNhd ℂ f (ball q r)) (hbound : ∀ p ∈ ball q r, ‖f p‖ ≤ M)
    (p : E) (hp : p ∈ ball q (r / 2)) : ‖fderiv ℂ f p‖ ≤ 8 * M / r := by
  have hsub : ball p (r / 2) ⊆ ball q r := by
    intro z hz
    rw [mem_ball] at hp hz ⊢
    exact (dist_triangle z p q).trans_lt (by linarith only [hp, hz])
  have hh := analytic_ball_joint_jet_bound 1 f p (r / 2) M (half_pos hr)
    (hf.mono hsub) (fun z hz => hbound z (hsub hz))
  rw [norm_iteratedFDeriv_one] at hh
  exact hh.trans_eq (by simp only [protectedJetConstant]; ring)

theorem regularComplexTimeDirection_norm (N : ℕ) : ‖regularComplexTimeDirection N‖ = 1 := by
  simp [regularComplexTimeDirection, Prod.norm_def]

theorem regularComplexAngularDirection_norm {N : ℕ} (i : Fin N) :
    ‖regularComplexAngularDirection i‖ = 1 := by
  simp [regularComplexAngularDirection, Prod.norm_def, Pi.norm_single]

/-- The full analytic transport operator on the inner half-ball.
The divergence term is estimated together with the differentiated
amplitude term and every coordinate in the field. -/
theorem analyticTransportAmplitude_ball_bound {N : ℕ}
    (B : RegularJointSpace N → Fin N → ℂ) (b : RegularJointSpace N → ℂ)
    (q : RegularJointSpace N) (r L M : ℝ) (hr : 0 < r) (hL : 0 ≤ L)
    (hB : AnalyticOnNhd ℂ B (ball q r)) (hb : AnalyticOnNhd ℂ b (ball q r))
    (hBL : ∀ p ∈ ball q r, ‖B p‖ ≤ L) (hbM : ∀ p ∈ ball q r, ‖b p‖ ≤ M)
    (p : RegularJointSpace N) (hp : p ∈ ball q (r / 2)) :
    ‖analyticTransportAmplitude B b p‖ ≤ 8 / r * (1 + 2 * (N : ℝ) * L) * M := by
  have hpR : p ∈ ball q r := ball_subset_ball (by linarith only [hr] : r / 2 ≤ r) hp
  have hdb := analytic_ball_inner_fderiv_bound b q r M hr hb hbM p hp
  have hdB := analytic_ball_inner_fderiv_bound B q r L hr hB hBL p hp
  have htime : ‖fderiv ℂ b p (regularComplexTimeDirection N)‖ ≤ 8 * M / r := by
    exact ((fderiv ℂ b p).le_opNorm _).trans (by simpa only [regularComplexTimeDirection_norm, mul_one] using hdb)
  have hbpartial (i : Fin N) : ‖fderiv ℂ b p (regularComplexAngularDirection i)‖ ≤ 8 * M / r := by
    exact ((fderiv ℂ b p).le_opNorm _).trans (by simpa only [regularComplexAngularDirection_norm, mul_one] using hdb)
  have hBpartial (i : Fin N) : ‖fderiv ℂ B p (regularComplexAngularDirection i) i‖ ≤ 8 * L / r := by
    exact (norm_le_pi_norm _ i).trans (((fderiv ℂ B p).le_opNorm _).trans
      (by simpa only [regularComplexAngularDirection_norm, mul_one] using hdB))
  have hBi (i : Fin N) : ‖B p i‖ ≤ L := (norm_le_pi_norm _ i).trans (hBL p hpR)
  have hfirst : ‖∑ i, B p i * fderiv ℂ b p (regularComplexAngularDirection i)‖ ≤
      (N : ℝ) * (L * (8 * M / r)) := by
    calc
      _ ≤ ∑ i, ‖B p i * fderiv ℂ b p (regularComplexAngularDirection i)‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin N, L * (8 * M / r) := by
        apply Finset.sum_le_sum
        intro i _
        rw [norm_mul]
        exact mul_le_mul (hBi i) (hbpartial i) (norm_nonneg _) hL
      _ = _ := by simp
  have hdiv : ‖∑ i, fderiv ℂ B p (regularComplexAngularDirection i) i‖ ≤ (N : ℝ) * (8 * L / r) := by
    exact (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun i _ => hBpartial i)).trans_eq (by simp))
  have hlast : ‖(∑ i, fderiv ℂ B p (regularComplexAngularDirection i) i) * b p‖ ≤
      ((N : ℝ) * (8 * L / r)) * M := by
    rw [norm_mul]
    exact mul_le_mul hdiv (hbM p hpR) (norm_nonneg _) (by positivity)
  unfold analyticTransportAmplitude
  calc
    _ ≤ ‖fderiv ℂ b p (regularComplexTimeDirection N) +
        ∑ i, B p i * fderiv ℂ b p (regularComplexAngularDirection i)‖ +
          ‖(∑ i, fderiv ℂ B p (regularComplexAngularDirection i) i) * b p‖ := norm_add_le _ _
    _ ≤ (‖fderiv ℂ b p (regularComplexTimeDirection N)‖ +
        ‖∑ i, B p i * fderiv ℂ b p (regularComplexAngularDirection i)‖) +
          ‖(∑ i, fderiv ℂ B p (regularComplexAngularDirection i) i) * b p‖ :=
      add_le_add (norm_add_le _ _) le_rfl
    _ ≤ (8 * M / r + (N : ℝ) * (L * (8 * M / r))) +
        ((N : ℝ) * (8 * L / r)) * M := add_le_add (add_le_add htime hfirst) hlast
    _ = _ := by ring

end IsingBulk.AnisoF002.Isotropic
