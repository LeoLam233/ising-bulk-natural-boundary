import IsingBulk.AnisoF002.NegativeHT.SimplePoleResidue

/-!
# Differential and simple residue along the constructed moving pole

The first differential of T is computed from the exact phase-level
equation.  It vanishes on the actual zero-sum displacement directions.
The temperature derivative remains nonzero near each fixed-n center,
and resonance then yields the genuine phase-kernel residue along T.
No dimension-uniform neighborhood or full numerator estimate is claimed.
-/

namespace IsingBulk.AnisoF002.NegativeHT

open Filter
open scoped Topology BigOperators

noncomputable section

/-- The cosh identity and center value force the exact local derivative
of any analytic branch satisfying the constructed branch conditions. -/
theorem local_negative_phase_derivative_unique (B : ℂ → ℂ) (φ d : ℝ)
    (hφ : Real.sin φ ≠ 0) (hB : AnalyticAt ℂ B ((1-Real.cos d : ℝ):ℂ))
    {g : ℂ × ℂ → ℂ}
    (hga : AnalyticAt ℂ g ((1-Real.cos d : ℝ),(d:ℂ)))
    (hgv : g ((1-Real.cos d : ℝ),(d:ℂ))=(φ:ℂ)*Complex.I)
    (hge : ∀ᶠ a in 𝓝 ((1-Real.cos d : ℝ),(d:ℂ)),
      Complex.cosh (g a)=localNegativeDispersion B φ a) :
    HasFDerivAt g
      ((((Real.sin φ:ℂ)*Complex.I)⁻¹*B ((1-Real.cos d : ℝ):ℂ)) •
        ContinuousLinearMap.fst ℂ ℂ ℂ -
       (((Real.sin φ:ℂ)*Complex.I)⁻¹*B ((1-Real.cos d : ℝ):ℂ)*(Real.sin d:ℂ)) •
        ContinuousLinearMap.snd ℂ ℂ ℂ)
      ((1-Real.cos d : ℝ),(d:ℂ)) := by
  have hs0 : (Real.sin φ:ℂ)*Complex.I ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hφ) Complex.I_ne_zero
  have hg := hga.differentiableAt.hasFDerivAt
  have hc := hg.ccosh
  have hw := (localNegativeDispersion_hasFDerivAt B φ d hB).congr_of_eventuallyEq hge
  have he := hc.unique hw
  rw [hgv, Complex.sinh_mul_I, ← Complex.ofReal_sin] at he
  have hh := congrArg (fun L : (ℂ × ℂ) →L[ℂ] ℂ =>
    ((Real.sin φ:ℂ)*Complex.I)⁻¹ • L) he
  simp only [smul_smul, inv_mul_cancel₀ hs0, one_smul, smul_sub] at hh
  exact hg.congr_fderiv (by simpa only [smul_smul, mul_assoc] using hh)

/-- Exact first differential of the moving level, with the full n factor. -/
theorem movingPole_fderiv_formula (n : ℕ) (g : ℂ × ℂ → ℂ) (d : ℝ) (τ c : ℂ)
    (hn : 0<n) (hc : c≠0)
    (hg : HasFDerivAt (negativePhaseSum n g d) (phaseSumDerivative n c d) (0,τ))
    {T : (Fin n → ℂ) → ℂ} (hTa : AnalyticAt ℂ T 0) (hTv : T 0=τ)
    (hzero : ∀ᶠ v in 𝓝 (0:Fin n → ℂ),
      negativePhaseSum n g d (v,T v)=negativePhaseSum n g d (0,τ)) :
    ∀ v : Fin n → ℂ,
      fderiv ℂ T 0 v = (Real.sin d:ℂ)/(n:ℂ)*(∑ i, v i) := by
  have hn0 : (n:ℂ)≠0 := by exact_mod_cast hn.ne'
  have htd := hTa.differentiableAt.hasFDerivAt
  have hp := (hasFDerivAt_id (0:Fin n → ℂ)).prodMk htd
  have hgp : HasFDerivAt (negativePhaseSum n g d) (phaseSumDerivative n c d) (0,T 0) := by
    rw [hTv]
    exact hg
  have hcomp := hgp.comp 0 hp
  have hconst : HasFDerivAt (fun v => negativePhaseSum n g d (v,T v))
      (0 : (Fin n → ℂ) →L[ℂ] ℂ) (0:Fin n → ℂ) :=
    (hasFDerivAt_const (𝕜 := ℂ) (negativePhaseSum n g d (0,τ))
      (0:Fin n → ℂ)).congr_of_eventuallyEq hzero
  have he := hcomp.unique hconst
  intro v
  have hv := congrArg (fun L : (Fin n → ℂ) →L[ℂ] ℂ => L v) he
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, zero_apply, phaseSumDerivative_apply] at hv
  have hz := (mul_eq_zero.mp hv).resolve_left hc
  have hnum := sub_eq_zero.mp hz
  calc
    _ = ((Real.sin d:ℂ)*(∑ i, v i))/(n:ℂ) := by
      apply (eq_div_iff hn0).mpr
      simpa only [mul_comm] using hnum
    _ = _ := by ring

/-- The temperature derivative of the phase level stays nonzero along
the moving pole in a neighborhood of each fixed-n center. -/
theorem eventually_movingPole_simple (n : ℕ) (g : ℂ × ℂ → ℂ) (d : ℝ) (τ c : ℂ)
    (hn : 0<n) (hc : c≠0)
    (hga : AnalyticAt ℂ (negativePhaseSum n g d) (0,τ))
    (hgd : HasFDerivAt (negativePhaseSum n g d) (phaseSumDerivative n c d) (0,τ))
    {T : (Fin n → ℂ) → ℂ} (hT : ContinuousAt T 0) (hTv : T 0=τ) :
    ∀ᶠ v in 𝓝 (0:Fin n → ℂ),
      DifferentiableAt ℂ (fun t => negativePhaseSum n g d (v,t)) (T v) ∧
      deriv (fun t => negativePhaseSum n g d (v,t)) (T v) ≠ 0 := by
  let F := negativePhaseSum n g d
  have hD : fderiv ℂ F (0,τ) (0,1) ≠ 0 := by
    rw [hgd.fderiv, phaseSumDerivative_apply]
    simpa only [Pi.zero_apply, Finset.sum_const_zero, mul_one, mul_zero, sub_zero] using
      mul_ne_zero hc (show (n:ℂ)≠0 by exact_mod_cast hn.ne')
  have hcont : ContinuousAt (fun a => fderiv ℂ F a (0,1)) (0,τ) :=
    hga.fderiv.continuousAt.clm_apply continuousAt_const
  have hne : ∀ᶠ a in 𝓝 ((0:Fin n → ℂ),τ), fderiv ℂ F a (0,1)≠0 :=
    hcont.eventually (eventually_ne_nhds hD)
  have hgraph : Tendsto (fun v : Fin n → ℂ => (v,T v)) (𝓝 0) (𝓝 (0,τ)) := by
    simpa only [hTv, id_eq] using (continuousAt_id.prodMk hT).tendsto
  filter_upwards [hgraph.eventually hga.eventually_analyticAt, hgraph.eventually hne] with v hva hvn
  have hs : HasDerivAt (fun t : ℂ => (v,t)) (0,1) (T v) :=
    (hasDerivAt_const (T v) v).prodMk (hasDerivAt_id (T v))
  have hh := hva.differentiableAt.hasFDerivAt.comp_hasDerivAt (T v) hs
  have hh' : HasDerivAt (fun t : ℂ => negativePhaseSum n g d (v,t))
      (fderiv ℂ (negativePhaseSum n g d) (v,T v) (0,1)) (T v) := by
    simpa only [Function.comp_def] using hh
  exact ⟨hh'.differentiableAt, by rwa [hh'.deriv]⟩

/-- The constructed pole, its zero-sum stationary property, and the
actual simple phase-kernel residue on a resonant edge. -/
theorem exists_resonant_moving_pole_residue (n : ℕ) (B : ℂ → ℂ) (φ d : ℝ)
    (hn : 0<n) (hφ : Real.sin φ ≠ 0)
    (hB : AnalyticAt ℂ B ((1-Real.cos d : ℝ):ℂ))
    (hB0 : B ((1-Real.cos d : ℝ):ℂ)≠0)
    (hres : Complex.exp ((n:ℂ)*((φ:ℂ)*Complex.I))=1) :
    ∃ g : ℂ × ℂ → ℂ, ∃ T : (Fin n → ℂ) → ℂ,
      AnalyticAt ℂ g ((1-Real.cos d : ℝ),(d:ℂ)) ∧
      g ((1-Real.cos d : ℝ),(d:ℂ))=(φ:ℂ)*Complex.I ∧
      (∀ᶠ a in 𝓝 ((1-Real.cos d : ℝ),(d:ℂ)),
        Complex.cosh (g a)=localNegativeDispersion B φ a) ∧
      AnalyticAt ℂ T 0 ∧ T 0=((1-Real.cos d : ℝ):ℂ) ∧
      (∀ v : Fin n → ℂ, (∑ i, v i)=0 → fderiv ℂ T 0 v=0) ∧
      ∀ᶠ v in 𝓝 (0:Fin n → ℂ),
        Complex.exp (negativePhaseSum n g d (v,T v))=1 ∧
        deriv (fun t => negativePhaseSum n g d (v,t)) (T v) ≠ 0 ∧
        Tendsto (fun t : ℂ => (t-T v)*
          phasePoleKernel (fun t => negativePhaseSum n g d (v,t)) t)
          (𝓝[≠] T v) (𝓝 (2/deriv (fun t => negativePhaseSum n g d (v,t)) (T v))) := by
  obtain ⟨g,T,hga,hgv,hge,hTa,hTv,hzero,_⟩ := exists_local_moving_pole n B φ d hn hφ hB hB0
  let τ : ℂ := ((1-Real.cos d : ℝ):ℂ)
  let c : ℂ := ((Real.sin φ:ℂ)*Complex.I)⁻¹*B τ
  have hc : c≠0 :=
    mul_ne_zero (inv_ne_zero (mul_ne_zero (by exact_mod_cast hφ) Complex.I_ne_zero)) hB0
  have hgd := local_negative_phase_derivative_unique B φ d hφ hB hga hgv hge
  have hΓd := negativePhaseSum_hasFDerivAt n g d τ c hgd
  have hΓa := negativePhaseSum_analyticAt n g d τ hga
  have hvalue : negativePhaseSum n g d (0,τ)=(n:ℂ)*((φ:ℂ)*Complex.I) := by
    have hv : g (τ,(d:ℂ))=(φ:ℂ)*Complex.I := hgv
    simp only [negativePhaseSum, Pi.zero_apply, add_zero, hv, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hlevel : ∀ᶠ v in 𝓝 (0:Fin n → ℂ),
      negativePhaseSum n g d (v,T v)=negativePhaseSum n g d (0,τ) := by
    rw [hvalue]
    exact hzero
  have hD := movingPole_fderiv_formula n g d τ c hn hc hΓd hTa hTv hlevel
  refine ⟨g,T,hga,hgv,hge,hTa,hTv,?_,?_⟩
  · intro v hv
    rw [hD v,hv,mul_zero]
  · filter_upwards [hzero, eventually_movingPole_simple n g d τ c hn hc hΓa hΓd
      hTa.continuousAt hTv] with v hv hs
    have hr : Complex.exp (negativePhaseSum n g d (v,T v))=1 := by
      change Complex.exp (∑ i, g (T v,(d:ℂ)+v i))=1
      rw [hv]
      exact hres
    exact ⟨hr,hs.2,phasePoleKernel_residue hs.1.hasDerivAt hr hs.2⟩

end

end IsingBulk.AnisoF002.NegativeHT
