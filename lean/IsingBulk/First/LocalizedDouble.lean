import IsingBulk.First.AngularFubini

/-! The actual normalized double density as a single product Bochner integral.
Complement weights may depend on both angle families; selected residue weights
remain y-only, and the two representations are proved equal. -/
namespace IsingBulk.First
noncomputable section
open Set MeasureTheory

def localizedDoubleAngleDensity {N : ℕ} (r : ℝ) (s : ℂ)
    (w : ((Fin N → ℝ) × (Fin N → ℝ)) → ℝ)
    (p : (Fin N → ℝ) × (Fin N → ℝ)) : ℂ :=
  (w p : ℂ)*angleProductJacobian r p.2*angleProductJacobian r p.1*
    doubleDensity s (angleTuple r p.1) (angleTuple r p.2)

def localizedDoubleFormFactor (N : ℕ) (r : ℝ) (s : ℂ)
    (w : ((Fin N → ℝ) × (Fin N → ℝ)) → ℝ) : ℂ :=
  (N.factorial : ℂ)⁻¹ * ∫ p in angleBox N ×ˢ angleBox N, localizedDoubleAngleDensity r s w p

theorem localizedDoubleAngleDensity_continuous (N : ℕ) (hN : 0 < N) (r : ℝ) (s : ℂ)
    (z : ℂ → ℂ)
    (h : ∀ θ : Fin N → ℝ, ResidueAdmissible r s (angleTuple r θ)
      (fun i => z (anglePoint r (θ i))))
    (w : ((Fin N → ℝ) × (Fin N → ℝ)) → ℝ) (hw : Continuous w) :
    Continuous (localizedDoubleAngleDensity r s w) := by
  have hD := doubleDensity_continuous_angles N hN r s z h
  have hJ := angleProductJacobian_continuous (N := N) r
  have hW : Continuous (fun p => (w p : ℂ)) := Complex.continuous_ofReal.comp hw
  convert! ((hW.mul (hJ.comp continuous_snd)).mul (hJ.comp continuous_fst)).mul hD using 1

theorem localizedDoubleAngleDensity_integrable (N : ℕ) (hN : 0 < N) (r : ℝ) (s : ℂ)
    (z : ℂ → ℂ)
    (h : ∀ θ : Fin N → ℝ, ResidueAdmissible r s (angleTuple r θ)
      (fun i => z (anglePoint r (θ i))))
    (w : ((Fin N → ℝ) × (Fin N → ℝ)) → ℝ) (hw : Continuous w) :
    IntegrableOn (localizedDoubleAngleDensity r s w) (angleBox N ×ˢ angleBox N) :=
  (localizedDoubleAngleDensity_continuous N hN r s z h w hw).continuousOn.integrableOn_compact
    (isCompact_Icc.prod isCompact_Icc)

/-- The same y-only weighted object before residues, now as one product integral. -/
theorem weightedDoubleFormFactor_eq_product_integral (N : ℕ) (hN : 0 < N) (r : ℝ) (s : ℂ)
    (z : ℂ → ℂ)
    (h : ∀ θ : Fin N → ℝ, ResidueAdmissible r s (angleTuple r θ)
      (fun i => z (anglePoint r (θ i))))
    (w : (Fin N → ℝ) → ℝ) (hw : Continuous w) :
    weightedDoubleFormFactor N r s w = localizedDoubleFormFactor N r s (fun p => w p.2) := by
  have hD := doubleDensity_continuous_angles N hN r s z h
  have hJ := angleProductJacobian_continuous (N := N) r
  have hW : Continuous (fun θ => (w θ : ℂ)) := Complex.continuous_ofReal.comp hw
  have houter : Continuous (fun θ : Fin N → ℝ => (w θ : ℂ)*angleProductJacobian r θ *
      multiCircleIntegral r N (fun x => doubleDensity s x (angleTuple r θ))) :=
    (hW.mul hJ).mul (residue_inner_continuous_angles N hN r s z h)
  have hinner (θ : Fin N → ℝ) : multiCircleIntegral r N
      (fun x => doubleDensity s x (angleTuple r θ)) =
      ∫ ξ in angleBox N, angleProductJacobian r ξ * doubleDensity s (angleTuple r ξ) (angleTuple r θ) := by
    rw [multiCircleIntegral_eq_angle]
    apply multiAngleIntegral_eq_box
    have hm : Continuous (fun ξ : Fin N → ℝ => (ξ, θ)) := continuous_id.prodMk continuous_const
    convert! hJ.mul (hD.comp hm) using 1
  have hI : IntegrableOn (localizedDoubleAngleDensity r s (fun p => w p.2))
      (angleBox N ×ˢ angleBox N) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact localizedDoubleAngleDensity_integrable N hN r s z h _ (hw.comp continuous_snd)
  unfold weightedDoubleFormFactor localizedDoubleFormFactor
  congr 1
  rw [multiAngleIntegral_eq_box N _ houter]
  rw [Measure.volume_eq_prod, setIntegral_prod_reverse volume volume _ _ _ hI]
  apply setIntegral_congr_fun measurableSet_Icc
  intro θ _
  dsimp only
  rw [hinner]
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Icc
  intro ξ _
  dsimp only [localizedDoubleAngleDensity]
  ring

/-- The unrestricted original normalized double object is the unweighted
product-angular integral used for complement localization. -/
theorem doubleFormFactor_eq_product_integral (N : ℕ) (hN : 0 < N) (r : ℝ) (s : ℂ)
    (z : ℂ → ℂ)
    (h : ∀ θ : Fin N → ℝ, ResidueAdmissible r s (angleTuple r θ)
      (fun i => z (anglePoint r (θ i)))) :
    doubleFormFactor N r s = localizedDoubleFormFactor N r s (fun _ => 1) := by
  rw [← weightedDoubleFormFactor_one]
  exact weightedDoubleFormFactor_eq_product_integral N hN r s z h _ continuous_const

end
end IsingBulk.First
