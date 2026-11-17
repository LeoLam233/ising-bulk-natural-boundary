import IsingBulk.AnisoF002.NegativeHT.CenterPhaseLimit
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Construction of the local negative-HT spectral phase

F002 `eq:jets_setting` and the real-cycle pole construction use the branch
of cosh inverse taking cos(phi) to i*phi.  This file constructs that
analytic branch by the inverse function theorem, then composes it with
the literal local dispersion relation.  It does not postulate an arcosh
branch or identify a global physical branch without a uniqueness proof.
-/

namespace IsingBulk.AnisoF002.NegativeHT

open Filter
open scoped Topology

noncomputable section

/-- A local analytic cosh inverse with the exact negative-HT center value. -/
theorem exists_local_cosh_inverse (φ : ℝ) (hφ : Real.sin φ ≠ 0) :
    ∃ G : ℂ → ℂ,
      AnalyticAt ℂ G (Real.cos φ : ℂ) ∧
      G (Real.cos φ : ℂ) = (φ : ℂ)*Complex.I ∧
      HasDerivAt G (((Real.sin φ : ℂ)*Complex.I)⁻¹) (Real.cos φ : ℂ) ∧
      ∀ᶠ z in 𝓝 (Real.cos φ : ℂ), Complex.cosh (G z) = z := by
  let y : ℂ := (φ : ℂ)*Complex.I
  have hc : Complex.cosh y = (Real.cos φ : ℂ) := by
    simp only [y, Complex.cosh_mul_I, ← Complex.ofReal_cos]
  have hs : Complex.sinh y = (Real.sin φ : ℂ)*Complex.I := by
    simp only [y, Complex.sinh_mul_I, ← Complex.ofReal_sin]
  have hs0 : Complex.sinh y ≠ 0 := by
    rw [hs]
    exact mul_ne_zero (by exact_mod_cast hφ) Complex.I_ne_zero
  have hd := Complex.hasStrictDerivAt_cosh y
  let H := (hd.hasStrictFDerivAt_equiv hs0).toOpenPartialHomeomorph Complex.cosh
  have hm : y ∈ H.source := (hd.hasStrictFDerivAt_equiv hs0).mem_toOpenPartialHomeomorph_source
  have ha : AnalyticAt ℂ H.symm (Real.cos φ : ℂ) := by
    rw [← hc]
    exact H.analyticAt_symm' hm Complex.analyticAt_cosh
      (hd.hasStrictFDerivAt_equiv hs0).hasFDerivAt.fderiv
  have hv : H.symm (Real.cos φ : ℂ) = y := by
    rw [← hc]
    exact H.left_inv hm
  have he : ∀ᶠ z in 𝓝 (Real.cos φ : ℂ), Complex.cosh (H.symm z) = z := by
    rw [← hc]
    exact H.eventually_right_inverse' hm
  have hi : HasDerivAt H.symm (((Real.sin φ : ℂ)*Complex.I)⁻¹)
      (Real.cos φ : ℂ) := by
    have hf : HasDerivAt Complex.cosh (Complex.sinh y) (H.symm (Real.cos φ : ℂ)) := by
      rw [hv]
      exact hd.hasDerivAt
    simpa only [hs] using hf.of_local_left_inverse ha.continuousAt hs0 he
  exact ⟨H.symm, ha, hv, hi, he⟩

/-- The literal local dispersion relation before taking its chosen branch. -/
def localNegativeDispersion (B : ℂ → ℂ) (φ : ℝ) (a : ℂ × ℂ) : ℂ :=
  (Real.cos φ : ℂ)+B a.1*(a.1-(1-Complex.cos a.2))

theorem localNegativeDispersion_center (B : ℂ → ℂ) (φ d : ℝ) :
    localNegativeDispersion B φ ((1-Real.cos d : ℝ), (d : ℂ)) =
      (Real.cos φ : ℂ) := by
  simp [localNegativeDispersion, ← Complex.ofReal_cos]

/-- Exact joint derivative at the pole center; the derivative of B drops
out because the centered dispersion displacement vanishes. -/
theorem localNegativeDispersion_hasFDerivAt (B : ℂ → ℂ) (φ d : ℝ)
    (hB : AnalyticAt ℂ B ((1-Real.cos d : ℝ) : ℂ)) :
    HasFDerivAt (localNegativeDispersion B φ)
      (B ((1-Real.cos d : ℝ) : ℂ) • ContinuousLinearMap.fst ℂ ℂ ℂ -
       (B ((1-Real.cos d : ℝ) : ℂ)*(Real.sin d : ℂ)) • ContinuousLinearMap.snd ℂ ℂ ℂ)
      ((1-Real.cos d : ℝ), (d : ℂ)) := by
  let p : ℂ × ℂ := ((1-Real.cos d : ℝ), (d : ℂ))
  let u : (ℂ × ℂ) →L[ℂ] ℂ := ContinuousLinearMap.fst ℂ ℂ ℂ
  let v : (ℂ × ℂ) →L[ℂ] ℂ := ContinuousLinearMap.snd ℂ ℂ ℂ
  have ht : HasFDerivAt (fun a : ℂ × ℂ => a.1) u p := u.hasFDerivAt
  have hd : HasFDerivAt (fun a : ℂ × ℂ => a.2) v p := v.hasFDerivAt
  have hb := hB.differentiableAt.hasDerivAt.comp_hasFDerivAt p ht
  have he := (hb.mul (ht.sub ((hasFDerivAt_const (1:ℂ) p).sub hd.ccos))).const_add
    (Real.cos φ : ℂ)
  convert he using 1
  · rfl
  · apply ContinuousLinearMap.ext
    intro a
    simp [p, u, v, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    ring

/-- A joint analytic branch of the actual local dispersion, together with
its exact center derivative.  Global physical-branch identification and
uniform-in-n neighborhoods remain separate obligations. -/
theorem exists_local_negative_phase (B : ℂ → ℂ) (φ d : ℝ)
    (hφ : Real.sin φ ≠ 0) (hB : AnalyticAt ℂ B ((1-Real.cos d : ℝ) : ℂ)) :
    ∃ g : ℂ × ℂ → ℂ,
      AnalyticAt ℂ g ((1-Real.cos d : ℝ), (d : ℂ)) ∧
      g ((1-Real.cos d : ℝ), (d : ℂ)) = (φ : ℂ)*Complex.I ∧
      HasFDerivAt g
        ((((Real.sin φ : ℂ)*Complex.I)⁻¹*B ((1-Real.cos d : ℝ) : ℂ)) •
          ContinuousLinearMap.fst ℂ ℂ ℂ -
         (((Real.sin φ : ℂ)*Complex.I)⁻¹*B ((1-Real.cos d : ℝ) : ℂ)*(Real.sin d : ℂ)) •
          ContinuousLinearMap.snd ℂ ℂ ℂ)
        ((1-Real.cos d : ℝ), (d : ℂ)) ∧
      ∀ᶠ a in 𝓝 ((1-Real.cos d : ℝ), (d : ℂ)),
        Complex.cosh (g a) = localNegativeDispersion B φ a := by
  obtain ⟨G, hG, hGc, hGd, hGi⟩ := exists_local_cosh_inverse φ hφ
  let p : ℂ × ℂ := ((1-Real.cos d : ℝ), (d : ℂ))
  have hWc : localNegativeDispersion B φ p = (Real.cos φ : ℂ) :=
    localNegativeDispersion_center B φ d
  have hWa : AnalyticAt ℂ (localNegativeDispersion B φ) p := by
    have hb : AnalyticAt ℂ (fun a : ℂ × ℂ => B a.1) p :=
      hB.comp_of_eq (show AnalyticAt ℂ (fun a : ℂ × ℂ => a.1) p from analyticAt_fst) rfl
    exact analyticAt_const.add (hb.mul
      (analyticAt_fst.sub (analyticAt_const.sub (Complex.analyticAt_cos.comp analyticAt_snd))))
  let g : ℂ × ℂ → ℂ := G ∘ localNegativeDispersion B φ
  have hga : AnalyticAt ℂ g p := hG.comp_of_eq hWa hWc
  refine ⟨g, hga, ?_, ?_, ?_⟩
  · change G (localNegativeDispersion B φ p) = _
    rw [hWc]
    exact hGc
  · have hd := hGd.comp_hasFDerivAt_of_eq p
      (localNegativeDispersion_hasFDerivAt B φ d hB) hWc.symm
    simpa only [smul_sub, smul_smul, mul_assoc] using hd
  · have ht := hWa.continuousAt.tendsto
    rw [hWc] at ht
    exact ht.eventually hGi

end

end IsingBulk.AnisoF002.NegativeHT
