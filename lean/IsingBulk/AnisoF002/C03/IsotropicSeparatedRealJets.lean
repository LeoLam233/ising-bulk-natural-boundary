import IsingBulk.AnisoF002.C03.IsotropicScaledWordJets
import IsingBulk.AnisoF002.C03.IsotropicSeparatedWordSumBounds

/-!
# First real jets of the complete separated word sum

The map to the regular coordinates and the real angular cutoff are both
differentiated.  The remaining angular derivative budget is explicitly
one larger than the number of transport steps.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set Metric
open scoped Topology BigOperators

theorem fderiv_holomorphic_pullback_product_bound
    {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    (q : E → G) (F : G → ℂ) (g : E → ℂ) (x : E)
    (hq : DifferentiableAt ℝ q x) (hF : DifferentiableAt ℂ F (q x))
    (hg : DifferentiableAt ℝ g x)
    {M₀ M₁ G₀ G₁ Q : ℝ} (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁)
    (hG₀ : 0 ≤ G₀) (_hG₁ : 0 ≤ G₁) (_hQ : 0 ≤ Q)
    (hF₀ : ‖F (q x)‖ ≤ M₀) (hF₁ : ‖fderiv ℂ F (q x)‖ ≤ M₁)
    (hg₀ : ‖g x‖ ≤ G₀) (hg₁ : ‖fderiv ℝ g x‖ ≤ G₁)
    (hq₁ : ‖fderiv ℝ q x‖ ≤ Q) :
    ‖fderiv ℝ (fun y => F (q y) * g y) x‖ ≤ M₀ * G₁ + G₀ * M₁ * Q := by
  have hd := (hF.hasFDerivAt.restrictScalars ℝ).comp x hq.hasFDerivAt
  simp only [Function.comp_def] at hd
  have hcomp : ‖fderiv ℝ (fun y => F (q y)) x‖ ≤ M₁ * Q := by
    rw [hd.fderiv]
    exact ((ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul (by simpa only [ContinuousLinearMap.norm_restrictScalars] using hF₁)
        hq₁ (norm_nonneg _) hM₁))
  rw [fderiv_fun_mul hd.differentiableAt hg]
  calc
    _ ≤ ‖F (q x) • fderiv ℝ g x‖ + ‖g x • fderiv ℝ (fun y => F (q y)) x‖ := norm_add_le _ _
    _ = ‖F (q x)‖ * ‖fderiv ℝ g x‖ + ‖g x‖ * ‖fderiv ℝ (fun y => F (q y)) x‖ := by
      rw [norm_smul, norm_smul]
    _ ≤ M₀ * G₁ + G₀ * (M₁ * Q) :=
      add_le_add (mul_le_mul hF₀ hg₁ (norm_nonneg _) hM₀)
        (mul_le_mul hg₀ hcomp (norm_nonneg _) hG₀)
    _ = _ := by ring

theorem separatedWordSum_first_real_jet_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {N : ℕ}
    (B K : RegularJointSpace N → Fin N → ℂ) (F : RegularJointSpace N → ℂ)
    (A : Fin N → Fin N → (Fin N → ℝ) → ℂ) (g : (Fin N → ℝ) → ℂ)
    (q : E → RegularJointSpace N) (θ : E → (Fin N → ℝ)) (x : E)
    (n k : ℕ) (hnk : n + 1 ≤ k)
    {CA Cg M₀ M₁ Q : ℝ} (hCA : 1 ≤ CA) (hCg : 0 ≤ Cg)
    (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁) (hQ : 0 ≤ Q)
    (hA : ∀ i j, FiniteJetControl k (A i j) CA) (hg : FiniteJetControl k g Cg)
    (hB : AnalyticAt ℂ B (q x)) (hK : ∀ j, AnalyticAt ℂ (fun p => K p j) (q x))
    (hF : AnalyticAt ℂ F (q x))
    (hFw₀ : ∀ w : TransportWord N n, ‖transportAnalyticWord B K F n w (q x)‖ ≤ M₀)
    (hFw₁ : ∀ w : TransportWord N n, ‖fderiv ℂ (transportAnalyticWord B K F n w) (q x)‖ ≤ M₁)
    (hq : DifferentiableAt ℝ q x) (hθ : DifferentiableAt ℝ θ x)
    (hqQ : ‖fderiv ℝ q x‖ ≤ Q) (hθ₁ : ‖fderiv ℝ θ x‖ ≤ 1) :
    ‖fderiv ℝ (fun y => ∑ w : TransportWord N n,
      transportAnalyticWord B K F n w (q y) * transportAngularWord A g n w (θ y)) x‖ ≤
      (Fintype.card (TransportWord N n) : ℝ) *
        (((2 ^ k * CA) ^ n * Cg) * (M₀ + M₁ * Q)) := by
  let LG := (2 ^ k * CA) ^ n * Cg
  have hLG : 0 ≤ LG := by dsimp [LG]; positivity
  have hnk' : n ≤ k := by omega
  have hkn : 1 ≤ k - n := by omega
  have hgw (w : TransportWord N n) :
      FiniteJetControl (k - n) (transportAngularWord A g n w) LG :=
    transportAngularWord_finite_jet_bound A g CA Cg hCA hCg hA hg n hnk' w
  have hgd (w : TransportWord N n) : DifferentiableAt ℝ (transportAngularWord A g n w) (θ x) :=
    (hgw w).smooth.differentiable (by norm_cast; omega) (θ x)
  have hga (w : TransportWord N n) : ‖fderiv ℝ (transportAngularWord A g n w) (θ x)‖ ≤ LG := by
    simpa only [norm_iteratedFDeriv_one] using (hgw w).bound 1 hkn (θ x)
  have hgg (w : TransportWord N n) :
      ‖fderiv ℝ (fun y => transportAngularWord A g n w (θ y)) x‖ ≤ LG := by
    have hd := (hgd w).hasFDerivAt.comp x hθ.hasFDerivAt
    simp only [Function.comp_def] at hd
    rw [hd.fderiv]
    exact ((ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul (hga w) hθ₁ (norm_nonneg _) hLG)).trans_eq (mul_one _)
  have hfa (w : TransportWord N n) : AnalyticAt ℂ (transportAnalyticWord B K F n w) (q x) :=
    transportAnalyticWord_analyticAt B K F (q x) hB hK hF n w
  have hd (w : TransportWord N n) : DifferentiableAt ℝ
      (fun y => transportAnalyticWord B K F n w (q y) * transportAngularWord A g n w (θ y)) x :=
    (((hfa w).restrictScalars.differentiableAt).comp x hq).mul ((hgd w).comp x hθ)
  have hb (w : TransportWord N n) :
      ‖fderiv ℝ (fun y => transportAnalyticWord B K F n w (q y) *
        transportAngularWord A g n w (θ y)) x‖ ≤ LG * (M₀ + M₁ * Q) := by
    have hg₀ : ‖transportAngularWord A g n w (θ x)‖ ≤ LG := by
      simpa only [norm_iteratedFDeriv_zero] using (hgw w).bound 0 (Nat.zero_le _) (θ x)
    exact (fderiv_holomorphic_pullback_product_bound q (transportAnalyticWord B K F n w)
      (fun y => transportAngularWord A g n w (θ y)) x hq (hfa w).differentiableAt
      ((hgd w).comp x hθ) hM₀ hM₁ hLG hLG hQ (hFw₀ w) (hFw₁ w) hg₀ (hgg w) hqQ).trans_eq (by ring)
  rw [fderiv_fun_sum (fun w _ => hd w)]
  exact (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun w _ => hb w)).trans_eq (by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, LG]))

end
end IsingBulk.AnisoF002.Isotropic
