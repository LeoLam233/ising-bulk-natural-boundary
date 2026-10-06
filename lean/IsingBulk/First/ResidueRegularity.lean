import IsingBulk.First.ContourIntegrability

/-! The source integrals genuinely exist: continuity and compact angular
integrability are proved on the actual root/radius domain, including fixed weights. -/
namespace IsingBulk.First
noncomputable section
open Set MeasureTheory
open scoped BigOperators

theorem continuous_coordinateProduct {P : Type*} [TopologicalSpace P] {N : ℕ}
    (x : P → (Fin N → ℂ)) (hx : Continuous x) : Continuous (fun p => coordinateProduct (x p)) := by
  unfold coordinateProduct
  apply continuous_finsetProd
  intro i _
  exact (continuous_apply i).comp hx

theorem continuous_pairProduct {P : Type*} [TopologicalSpace P] {N : ℕ}
    (x : P → (Fin N → ℂ)) (hx : Continuous x) (hn : ∀ p i, ‖x p i‖ < 1) :
    Continuous (fun p => pairProduct (x p)) := by
  unfold pairProduct
  apply continuous_finsetProd
  intro i _
  apply continuous_finsetProd
  intro j _
  change Continuous (fun p => (x p i-x p j)/(1-x p i*x p j))
  have hi := (continuous_apply i).comp hx
  have hj := (continuous_apply j).comp hx
  exact (hi.sub hj).div (continuous_const.sub (hi.mul hj))
    (fun p => one_sub_mul_ne_zero_of_norm_lt_one (hn p i) (hn p j))

theorem doubleDensity_continuous_angles (N : ℕ) (hN : 0 < N) (r : ℝ) (s : ℂ)
    (z : ℂ → ℂ)
    (h : ∀ θ : Fin N → ℝ, ResidueAdmissible r s (angleTuple r θ)
      (fun i => z (anglePoint r (θ i)))) :
    Continuous (fun p : (Fin N → ℝ) × (Fin N → ℝ) =>
      doubleDensity s (angleTuple r p.1) (angleTuple r p.2)) := by
  have hr := (h (fun _ => 0)).radius_pos
  have hr1 := (h (fun _ => 0)).radius_lt_one
  let x : ((Fin N → ℝ) × (Fin N → ℝ)) → Fin N → ℂ := fun p => angleTuple r p.1
  let y : ((Fin N → ℝ) × (Fin N → ℝ)) → Fin N → ℂ := fun p => angleTuple r p.2
  have hx : Continuous x := angleTuple_continuous r |>.comp continuous_fst
  have hy : Continuous y := angleTuple_continuous r |>.comp continuous_snd
  have hxn : ∀ p i, ‖x p i‖ = r := fun p i => anglePoint_norm hr.le _
  have hyn : ∀ p i, ‖y p i‖ = r := fun p i => anglePoint_norm hr.le _
  have hx0 : ∀ p i, x p i ≠ 0 := by
    intro p i he
    have hn := hxn p i
    simp [he] at hn
    linarith
  have hy0 : ∀ p i, y p i ≠ 0 := by
    intro p i he
    have hn := hyn p i
    simp [he] at hn
    linarith
  have hxl : ∀ p i, ‖x p i‖ < 1 := fun p i => (hxn p i).trans_lt hr1
  have hyl : ∀ p i, ‖y p i‖ < 1 := fun p i => (hyn p i).trans_lt hr1
  have hX := continuous_coordinateProduct x hx
  have hY := continuous_coordinateProduct y hy
  have hX0 : ∀ p, coordinateProduct (x p) ≠ 0 := fun p =>
    Finset.prod_ne_zero_iff.mpr (fun i _ => hx0 p i)
  have hY0 : ∀ p, coordinateProduct (y p) ≠ 0 := fun p =>
    Finset.prod_ne_zero_iff.mpr (fun i _ => hy0 p i)
  have hDX : Continuous (fun p => ∏ i, (dispersion (x p i) (y p i) s)⁻¹) := by
    apply continuous_finsetProd
    intro i _
    have hi := (continuous_apply i).comp hx
    have hj := (continuous_apply i).comp hy
    have hD : Continuous (fun p => dispersion (x p i) (y p i) s) := by
      unfold dispersion
      exact (continuous_const.sub ((hi.add (hi.inv₀ (fun p => hx0 p i))).div_const 2)).sub
        ((hj.add (hj.inv₀ (fun p => hy0 p i))).div_const 2)
    apply hD.inv₀
    intro p
    exact dispersion_ne_zero_on_circle (h p.2) (hxn p i) i
  have hglob : Continuous (fun p =>
      ((coordinateProduct (x p))⁻¹+(coordinateProduct (y p))⁻¹) /
        ((1-coordinateProduct (x p))*(1-coordinateProduct (y p)))) :=
    ((hX.inv₀ hX0).add (hY.inv₀ hY0)).div
      ((continuous_const.sub hX).mul (continuous_const.sub hY))
      (fun p => mul_ne_zero (one_sub_coordinateProduct_ne_zero hN (hxl p))
        (one_sub_coordinateProduct_ne_zero hN (hyl p)))
  exact hglob.mul (((continuous_pairProduct x hx hxl).mul
    (continuous_pairProduct y hy hyl)).mul hDX)

/-- The normalized inner x integral depends continuously on all y angles. -/
theorem residue_inner_continuous_angles (N : ℕ) (hN : 0 < N) (r : ℝ) (s : ℂ)
    (z : ℂ → ℂ)
    (h : ∀ θ : Fin N → ℝ, ResidueAdmissible r s (angleTuple r θ)
      (fun i => z (anglePoint r (θ i)))) :
    Continuous (fun θ : Fin N → ℝ =>
      multiCircleIntegral r N (fun x => doubleDensity s x (angleTuple r θ))) := by
  simp_rw [multiCircleIntegral_eq_angle]
  apply continuous_multiAngleIntegral
  have hD := doubleDensity_continuous_angles N hN r s z h
  have hJ : Continuous (fun p : (Fin N → ℝ) × (Fin N → ℝ) => angleProductJacobian r p.2) :=
    (angleProductJacobian_continuous (N := N) r).comp continuous_snd
  have hswap : Continuous (fun p : (Fin N → ℝ) × (Fin N → ℝ) =>
      doubleDensity s (angleTuple r p.2) (angleTuple r p.1)) := by
    have hm : Continuous (fun p : (Fin N → ℝ) × (Fin N → ℝ) => (p.2, p.1)) :=
      continuous_snd.prodMk continuous_fst
    convert! hD.comp hm using 1
  exact hJ.mul hswap

/-- Continuity of the physical reduced density is derived from the integral
identity, rather than assumed as regularity of an arbitrary root selector. -/
theorem reducedDensity_continuous_angles (N : ℕ) (hN : 0 < N) (r : ℝ) (s : ℂ)
    (z : ℂ → ℂ)
    (h : ∀ θ : Fin N → ℝ, ResidueAdmissible r s (angleTuple r θ)
      (fun i => z (anglePoint r (θ i)))) :
    Continuous (fun θ : Fin N → ℝ =>
      reducedDensity (fun i => z (anglePoint r (θ i))) (angleTuple r θ)) := by
  have he : (fun θ : Fin N → ℝ => multiCircleIntegral r N
      (fun x => doubleDensity s x (angleTuple r θ))) =
      (fun θ : Fin N → ℝ => reducedDensity (fun i => z (anglePoint r (θ i))) (angleTuple r θ)) := by
    funext θ
    exact residue_inner_integral hN (h θ)
  rw [← he]
  exact residue_inner_continuous_angles N hN r s z h

/-- The complete normalized angular density, with both Jacobian products. -/
def weightedDoubleAngleDensity {N : ℕ} (r : ℝ) (s : ℂ) (w : (Fin N → ℝ) → ℝ)
    (p : (Fin N → ℝ) × (Fin N → ℝ)) : ℂ :=
  (w p.2 : ℂ) * angleProductJacobian r p.2 * angleProductJacobian r p.1 *
    doubleDensity s (angleTuple r p.1) (angleTuple r p.2)

def weightedReducedAngleDensity {N : ℕ} (r : ℝ) (z : ℂ → ℂ) (w : (Fin N → ℝ) → ℝ)
    (θ : Fin N → ℝ) : ℂ :=
  (w θ : ℂ) * angleProductJacobian r θ *
    reducedDensity (fun i => z (anglePoint r (θ i))) (angleTuple r θ)

theorem residue_integrals_exist (N : ℕ) (hN : 0 < N) (r : ℝ) (s : ℂ)
    (z : ℂ → ℂ) (w : (Fin N → ℝ) → ℝ) (hw : Continuous w)
    (h : ∀ θ : Fin N → ℝ, ResidueAdmissible r s (angleTuple r θ)
      (fun i => z (anglePoint r (θ i)))) :
    IntegrableOn (weightedDoubleAngleDensity r s w) (angleBox N ×ˢ angleBox N) ∧
    (∀ θ : Fin N → ℝ, AngleStagesIntegrable N (fun ξ => angleProductJacobian r ξ *
      doubleDensity s (angleTuple r ξ) (angleTuple r θ))) ∧
    AngleStagesIntegrable N (fun θ => (w θ : ℂ)*angleProductJacobian r θ *
      multiCircleIntegral r N (fun x => doubleDensity s x (angleTuple r θ))) ∧
    IntegrableOn (weightedReducedAngleDensity r z w) (angleBox N) ∧
    AngleStagesIntegrable N (weightedReducedAngleDensity r z w) := by
  have hD := doubleDensity_continuous_angles N hN r s z h
  have hJ := angleProductJacobian_continuous (N := N) r
  have hW : Continuous (fun θ => (w θ : ℂ)) := Complex.continuous_ofReal.comp hw
  have hfull : Continuous (weightedDoubleAngleDensity r s w) := by
    convert! (((hW.comp continuous_snd).mul (hJ.comp continuous_snd)).mul
      (hJ.comp continuous_fst)).mul hD using 1
  have hred : Continuous (weightedReducedAngleDensity r z w) := by
    convert! (hW.mul hJ).mul (reducedDensity_continuous_angles N hN r s z h) using 1
  refine ⟨hfull.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc), ?_, ?_,
    continuous_angleBox_integrable _ hred, continuous_angle_stages N _ hred⟩
  · intro θ
    apply continuous_angle_stages
    have hm : Continuous (fun ξ : Fin N → ℝ => (ξ, θ)) := continuous_id.prodMk continuous_const
    convert! hJ.mul (hD.comp hm) using 1
  · apply continuous_angle_stages
    exact (hW.mul hJ).mul (residue_inner_continuous_angles N hN r s z h)

end
end IsingBulk.First
