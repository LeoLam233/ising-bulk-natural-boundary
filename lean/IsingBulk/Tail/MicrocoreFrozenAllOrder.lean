import IsingBulk.Tail.MicrocoreAllOrder

/-! All orders retain a common phase-only factor. No collision factor or
simple Z denominator is differentiated or canceled against a singular quotient. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Jets IsingBulk.Lie
open scoped ContDiff BigOperators

theorem microcoreTermSum_differentiable {n : ℕ} (v θ : ℝ) (w : AngularSpace n → ℝ)
    (F : ℂ × (Fin (n+1) → ℂ) → ℂ) (j : ℕ) (s : ℂ) (x : AngularSpace n)
    (hw : ContDiff ℝ ∞ w) (h : MicrocoreJetPoint v θ s x)
    (hF : AnalyticAt ℂ F (s,chartMap v θ s x)) :
    DifferentiableAt ℂ (fun t => microcoreTermSum v θ w F j t x) s ∧
    DifferentiableAt ℝ (microcoreTermSum v θ w F j s) x := by
  have hT := microcoreJetTerms_analytic F j (s,chartMap v θ s x) hF h.regularA_analytic
  have hd := fun T hmem => MicrocoreJetTerm.source_differentiable T v θ s x w hw h.s_ne
    h.re_pos h.im_pos h.sin_ne (hT T hmem)
  have hV : ∀ i, DifferentiableAt ℝ (fun y => microcoreField v θ s y i) x := by
    intro i
    apply (microcoreField_hasFDerivAt v θ s x i _).differentiableAt
    intro hz
    simpa [hz] using h.g_pos i
  have he := lieStep_finite_sum (microcoreField v θ)
    ((microcoreJetTerms F j).map (fun T => T.sourceValue v θ w)) s x hV
    (by intro G hG; obtain ⟨T,hmem,rfl⟩ := List.mem_map.mp hG; exact (hd T hmem).1)
    (by intro G hG; obtain ⟨T,hmem,rfl⟩ := List.mem_map.mp hG; exact (hd T hmem).2)
  simp only [List.map_map,Function.comp_def] at he
  constructor
  · convert! he.1 using 1
  · convert! he.2.1 using 1

theorem microcore_frozen_factor_step {n : ℕ} (v θ : ℝ) (w : AngularSpace n → ℝ)
    (F : ℂ × (Fin (n+1) → ℂ) → ℂ) (Q : (Fin (n+1) → ℂ) → ℂ)
    (j : ℕ) (s : ℂ) (x : AngularSpace n) (hw : ContDiff ℝ ∞ w)
    (h : MicrocoreJetPoint v θ s x) (hF : AnalyticAt ℂ F (s,chartMap v θ s x))
    (hQ : DifferentiableAt ℂ Q (chartMap v θ s x)) :
    lieStep (microcoreField v θ)
      (fun t y => Q (chartMap v θ t y)*microcoreTermSum v θ w F j t y) s x =
      Q (chartMap v θ s x)*microcoreTermSum v θ w F (j+1) s x := by
  have hQs := (hQ.hasFDerivAt.comp_hasDerivAt s
    (chartMap_parameter v θ s x h.s_ne h.re_pos h.im_pos)).differentiableAt
  have hQx := ((hQ.hasFDerivAt.restrictScalars ℝ).comp x
    (chartMap_spatial v θ s x h.re_pos h.im_pos)).differentiableAt
  have hgn : ∀ i, angularG v θ (x i) ≠ 0 := fun i hz => by simpa [hz] using h.g_pos i
  have hV : ∀ i, DifferentiableAt ℝ (fun y => microcoreField v θ s y i) x :=
    fun i => (microcoreField_hasFDerivAt v θ s x i (hgn i)).differentiableAt
  obtain ⟨hS,hX⟩ := microcoreTermSum_differentiable v θ w F j s x hw h hF
  rw [lieStep_mul_frozen _ _ _ s x hQs hS hQx hX hV
    (microcore_transport_fixed_observable v θ s x Q h.s_ne h.re_pos h.im_pos hgn hQ)]
  rw [microcoreTermSum_step v θ w F j s x hw h hF]

theorem microcore_frozen_factor_all_order {n : ℕ} (v θ : ℝ) (w : AngularSpace n → ℝ)
    (F : ℂ × (Fin (n+1) → ℂ) → ℂ) (Q : (Fin (n+1) → ℂ) → ℂ)
    (U : Set ℂ) (R : Set (AngularSpace n)) (hU : IsOpen U) (hR : IsOpen R)
    (hw : ContDiff ℝ ∞ w) (hchart : ∀ s ∈ U, ∀ x ∈ R, MicrocoreJetPoint v θ s x)
    (hF : ∀ s ∈ U, ∀ x ∈ R, AnalyticAt ℂ F (s,chartMap v θ s x))
    (hQ : ∀ s ∈ U, ∀ x ∈ R, DifferentiableAt ℂ Q (chartMap v θ s x)) (j : ℕ) :
    ∀ s ∈ U, ∀ x ∈ R,
      ((lieStep (microcoreField v θ))^[j]
        (fun t y => Q (chartMap v θ t y)*
          ((w y:ℂ)*chartPullback v θ (fun t φ => F (t,φ)) t y))) s x =
      Q (chartMap v θ s x)*microcoreTermSum v θ w F j s x := by
  induction j with
  | zero => intro s _ x _; simp [microcoreTermSum,microcoreJetTerms,MicrocoreJetTerm.sourceValue,cutoffJet]
  | succ j ih =>
    intro s hs x hx
    rw [Function.iterate_succ_apply']
    rw [lieStep_congr_on (microcoreField v θ) hU hR ih hs hx]
    exact microcore_frozen_factor_step v θ w F Q j s x hw (hchart s hs x hx)
      (hF s hs x hx) (hQ s hs x hx)

def microcorePhaseFactor {N : ℕ} (φ : Fin N → ℂ) : ℂ :=
  microcoreVandermondeSquared φ/(1-Complex.exp (-Complex.I*∑ i, φ i))

theorem microcorePhaseFactor_differentiable {N : ℕ} (φ : Fin N → ℂ)
    (hZ : 1-Complex.exp (-Complex.I*∑ i, φ i) ≠ 0) :
    DifferentiableAt ℂ microcorePhaseFactor φ := by
  unfold microcorePhaseFactor
  have hP : DifferentiableAt ℂ (@microcoreVandermondeSquared N) φ :=
    microcoreVandermondeSquared_differentiable N φ
  have hD : DifferentiableAt ℂ (fun ψ : Fin N → ℂ => 1-Complex.exp (-Complex.I*∑ i, ψ i)) φ := by
    fun_prop
  convert! hP.mul (hD.inv hZ) using 1

end
end IsingBulk.Tail
