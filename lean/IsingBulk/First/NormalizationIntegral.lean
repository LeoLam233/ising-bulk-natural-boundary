import IsingBulk.First.NormalizationRegularity
import IsingBulk.First.FormFactorNormalization

/-! The exact full-site=onsite+2*offsite identity for actual normalized integrals,
with genuine absolute integrability and finite Fubini. -/
namespace IsingBulk.First
noncomputable section
open Set MeasureTheory

def doubleAngularDensityOf {N : ℕ} (r : ℝ)
    (f : (Fin N → ℂ) → (Fin N → ℂ) → ℂ)
    (p : (Fin N → ℝ) × (Fin N → ℝ)) : ℂ :=
  angleProductJacobian r p.2*angleProductJacobian r p.1*f (angleTuple r p.1) (angleTuple r p.2)

theorem doubleAngularDensityOf_continuous (N : ℕ) (r : ℝ)
    (f : (Fin N → ℂ) → (Fin N → ℂ) → ℂ)
    (hf : Continuous (fun p : (Fin N → ℝ) × (Fin N → ℝ) => f (angleTuple r p.1) (angleTuple r p.2))) :
    Continuous (doubleAngularDensityOf r f) := by
  have hJ := angleProductJacobian_continuous (N := N) r
  convert! ((hJ.comp continuous_snd).mul (hJ.comp continuous_fst)).mul hf using 1

theorem standardFormFactor_eq_onsite_add_double (N : ℕ) (hN : 0 < N)
    (r : ℝ) (s : ℂ) (z : ℂ → ℂ) (h : ScalarResidueAdmissible r s z) :
    standardFormFactor N r s = onsiteFormFactor N r s + 2*doubleFormFactor N r s := by
  have htuple : ∀ θ : Fin N → ℝ, ResidueAdmissible r s (angleTuple r θ)
      (fun i => z (anglePoint r (θ i))) := by
    intro θ
    apply h.toTuple N (angleTuple r θ)
    intro i
    exact anglePoint_norm h.radius_pos.le _
  have hD := doubleDensity_continuous_angles N hN r s z htuple
  obtain ⟨hO, hS⟩ := normalizationDensities_continuous_angles N hN r s z h
  let Fd := doubleAngularDensityOf r (doubleDensity (N := N) s)
  let Fo := doubleAngularDensityOf r (onsiteDensity (N := N) s)
  let Fs := doubleAngularDensityOf r (standardDensity (N := N) s)
  have hiD : IntegrableOn Fd (angleBox N ×ˢ angleBox N) :=
    (doubleAngularDensityOf_continuous N r _ hD).continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)
  have hiO : IntegrableOn Fo (angleBox N ×ˢ angleBox N) :=
    (doubleAngularDensityOf_continuous N r _ hO).continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)
  have hprod0 (θ : Fin N → ℝ) : coordinateProduct (angleTuple r θ) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _ hi
    have hn := anglePoint_norm h.radius_pos.le (θ i)
    change anglePoint r (θ i)=0 at hi
    rw [hi, norm_zero] at hn
    linarith [h.radius_pos]
  have hprod1 (θ : Fin N → ℝ) : 1-coordinateProduct (angleTuple r θ) ≠ 0 := by
    apply one_sub_coordinateProduct_ne_zero hN
    intro i
    change ‖anglePoint r (θ i)‖ < 1
    rw [anglePoint_norm h.radius_pos.le]
    exact h.radius_lt_one
  have he : Fs = fun p => Fo p+2*Fd p := by
    funext p
    have hp := standardDensity_eq_onsite_add_double s (angleTuple r p.1) (angleTuple r p.2)
      (hprod0 p.1) (hprod0 p.2) (hprod1 p.1) (hprod1 p.2)
    dsimp only [Fs, Fo, Fd, doubleAngularDensityOf]
    rw [hp]
    ring
  unfold standardFormFactor onsiteFormFactor doubleFormFactor
  rw [doubleCircleIntegral_eq_product N r (standardDensity s) hS,
    doubleCircleIntegral_eq_product N r (onsiteDensity s) hO,
    doubleCircleIntegral_eq_product N r (doubleDensity s) hD]
  change (N.factorial:ℂ)⁻¹ * (∫ p in angleBox N ×ˢ angleBox N, Fs p) =
    (N.factorial:ℂ)⁻¹ * (∫ p in angleBox N ×ˢ angleBox N, Fo p) +
      2*((N.factorial:ℂ)⁻¹ * (∫ p in angleBox N ×ˢ angleBox N, Fd p))
  rw [he, integral_add hiO (hiD.const_mul 2), integral_const_mul]
  ring

end
end IsingBulk.First
