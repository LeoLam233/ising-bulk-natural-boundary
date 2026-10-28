import IsingBulk.HT22.SeedFrameConversion.Bounds
import IsingBulk.Preferred22.SourceCutoffFrameJets
import IsingBulk.HT22.Anchor.BranchJets
import IsingBulk.Preferred22.FrameWeightedBounds

/-! Primitive inverse-factor control in the genuine fixed-v frame. Real smooth
cutoffs remain real functions throughout. The moving-q derivative is corrected
by the actual branch velocity before any frame-word conversion. -/
namespace IsingBulk.HT22.InverseFactorJets
noncomputable section
open Set Filter IsingBulk.Preferred22 IsingBulk.HT22.Tail
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false

/-- Local equality propagates through every literal shared frame word. -/
theorem sharedFrameJet_congr_open {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ)
    (F G : ℂ → (Fin N → ℝ) → ℂ) (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (he : ∀ z∈Ω, F z.1 z.2=G z.1 z.2) (xs : List (Option (Fin N)))
    (s : ℂ) (θ : Fin N → ℝ) (hz : (s,θ)∈Ω) :
    preferredFrameJet τ p m F xs s θ=preferredFrameJet τ p m G xs s θ := by
  induction xs generalizing s θ with
  | nil => exact he (s,θ) hz
  | cons a xs ih =>
    rw [preferredFrameJet_cons,preferredFrameJet_cons]
    exact preferredFrameStep_congr_open τ p m a _ _ Ω hΩ (fun z hz => ih z.1 z.2 hz) s θ hz

/-- The fixed-v inverse derivative is not the moving-q inverse derivative. -/
theorem inverseT_source_adapter {N : ℕ} {τ δ : ℝ} {p m : ℝ → ℝ}
    {s : ℂ} {θ : Fin N → ℝ} (h : PreferredFramePoint τ δ p m s θ) (i : Fin N) :
    inverseT s (sourceCoordinate τ p m s θ i)=
      preferredSourceUDot s (preferredSourceCoordinate τ p m s θ i)-
      preferredSourceUQ s (preferredSourceCoordinate τ p m s θ i)*deriv preferredMovingBranch s := by
  rw [inverseT_moving_adapter s _ (framePoint_inverse_analytic h i)
    (preferredMovingBranch_analyticAt_upper s h.trace_im).differentiableAt,
    inverseV_moving_adapter,sourceCoordinate_moving_adapter]

/-- Both old analytic factors have mixed smooth pullbacks on actual real charts. -/
theorem shared_inverse_factors_mixed {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (Ω : Set (ℂ × (Fin N → ℝ)))
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2) :
    (∀ i, PreferredMixedSmoothOn (fun z =>
      preferredSourceUQ z.1 (preferredSourceCoordinate τ p m z.1 z.2 i)) Ω) ∧
    (∀ i, PreferredMixedSmoothOn (fun z =>
      preferredSourceUDot z.1 (preferredSourceCoordinate τ p m z.1 z.2 i)) Ω) ∧
    PreferredMixedSmoothOn (fun z => deriv preferredMovingBranch z.1) Ω := by
  have hjet (F : ℂ → ℂ → ℂ)
      (hF : ∀ z∈Ω, ∀ i, AnalyticAt ℂ (fun x : ℂ × ℂ => F x.1 x.2)
        (z.1,preferredSourceCoordinate τ p m z.1 z.2 i)) (i : Fin N) :
      PreferredMixedSmoothOn (fun z => F z.1 (preferredSourceCoordinate τ p m z.1 z.2 i)) Ω := by
    apply preferred_analytic_pullback_mixed τ δ p m hp hm Ω hpoint (fun x => F x.1 (x.2 i))
    intro z hz
    exact AnalyticAt.comp (f := fun x : ℂ × (Fin N → ℂ) => (x.1,x.2 i))
      (g := fun x : ℂ × ℂ => F x.1 x.2) (hF z hz i) ((preferredOneProjection i).analyticAt _)
  refine ⟨hjet preferredSourceUQ (fun z hz i =>
      preferredSourceUQ_analyticAt_of_joint _ _ ((hpoint z hz).inverse_analytic i)),
    hjet preferredSourceUDot (fun z hz i =>
      preferredSourceUDot_analyticAt_of_joint _ _ ((hpoint z hz).inverse_analytic i)),?_⟩
  intro z hz
  have ha := (preferredMovingBranch_analyticAt_upper z.1 (hpoint z hz).trace_im).deriv
  exact ⟨ha.contDiffAt.restrict_scalars ℝ |>.comp z contDiffAt_fst,ha.differentiableAt⟩

/-- The actual fixed-v inverse factors are smooth independently of covariance. -/
theorem inverse_factors_mixed {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2) :
    (∀ i, PreferredMixedSmoothOn (fun z => inverseV z.1 (sourceCoordinate τ p m z.1 z.2 i)) Ω) ∧
    (∀ i, PreferredMixedSmoothOn (fun z => inverseT z.1 (sourceCoordinate τ p m z.1 z.2 i)) Ω) := by
  obtain ⟨hq,hd,hb⟩ := shared_inverse_factors_mixed τ δ p m hp hm Ω hpoint
  constructor
  · intro i
    simpa only [inverseV_moving_adapter,sourceCoordinate_moving_adapter] using hq i
  · intro i
    apply ((hd i).sub ((hq i).mul hb)).congr hΩ
    intro z hz
    exact (inverseT_source_adapter (hpoint z hz) i).symm

/-- Old-frame control of the actual fixed-v inverse derivative, including all
branch-velocity Leibniz terms. This is only an internal quantitative adapter. -/
theorem shared_inverseT_frame_bound {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
    (s : ℂ) (θ : Fin N → ℝ) (hz : (s,θ)∈Ω) (J : ℕ)
    (A B : ℝ) (hA : 0≤A) (hB : 0≤B)
    (hU : ∀ xs : List (Option (Fin N)), xs.length≤J → ∀ i,
      ‖preferredFrameJet τ p m
        (fun t x => preferredSourceUQ t (preferredSourceCoordinate τ p m t x i)) xs s θ‖≤A ∧
      ‖preferredFrameJet τ p m
        (fun t x => preferredSourceUDot t (preferredSourceCoordinate τ p m t x i)) xs s θ‖≤A)
    (hb : ∀ xs : List (Option (Fin N)), xs.length≤J →
      ‖preferredFrameJet τ p m (fun t _ => deriv preferredMovingBranch t) xs s θ‖≤B)
    (xs : List (Option (Fin N))) (hxs : xs.length≤J) (i : Fin N) :
    ‖preferredFrameJet τ p m
      (fun t x => inverseT t (sourceCoordinate τ p m t x i)) xs s θ‖≤A+2^J*A*B := by
  obtain ⟨hq,hd,hbm⟩ := shared_inverse_factors_mixed τ δ p m hp hm Ω hpoint
  rw [sharedFrameJet_congr_open τ p m _
    (fun t x => preferredSourceUDot t (preferredSourceCoordinate τ p m t x i)-
      preferredSourceUQ t (preferredSourceCoordinate τ p m t x i)*deriv preferredMovingBranch t)
    Ω hΩ (fun z hz => inverseT_source_adapter (hpoint z hz) i) xs s θ hz,
    preferredFrameJet_sub τ δ p m hp hm Ω hΩ hpoint _ _ (hd i) ((hq i).mul hbm) xs s θ hz]
  apply (norm_sub_le _ _).trans
  apply add_le_add ((hU xs hxs i).2)
  exact preferredFrameJet_mul_bound τ δ p m hp hm Ω hΩ hpoint _ _ (hq i) hbm s θ hz
    J A B hA hB (fun ys hys => (hU ys hys i).1) hb xs hxs

/-- Converting finite words costs only a fixed-order polynomial in N. -/
theorem conversion_polynomial_growth (N J E : ℕ) (hN : 0<N) (A B : ℝ)
    (hA : 0≤A) (hB : 0≤B) :
    ((N:ℝ)+2)^J*(B*(A*(N:ℝ)^E))≤(3^J*B*A)*(N:ℝ)^(E+J) := by
  have hn : (1:ℝ)≤N := by exact_mod_cast hN
  calc
    _ ≤ ((3:ℝ)*N)^J*(B*(A*(N:ℝ)^E)) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by linarith) J) (by positivity)
    _ = _ := by rw [mul_pow,pow_add]; ring

end
end IsingBulk.HT22.InverseFactorJets
