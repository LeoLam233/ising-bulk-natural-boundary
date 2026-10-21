import IsingBulk.HT.Contour.OnsitePiola
import IsingBulk.Tail.SelectorSmoothDensity

namespace IsingBulk.HT.Contour
noncomputable section
open IsingBulk.First IsingBulk.Tail Filter Set
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false

 theorem onsiteLogDensity_contDiffAt_real (N : ℕ) (_hN : 0 < N) (s : ℂ) (ℓ : Fin N → ℂ)
    (hW : ∀ i, 0 < (sourceW s (Complex.exp (ℓ i))).im) :
    ContDiffAt ℝ ∞ (onsiteLogDensity N s) ℓ := by
  let y : (Fin N → ℂ) → Fin N → ℂ := fun x i => Complex.exp (x i)
  let z : (Fin N → ℂ) → Fin N → ℂ := fun x i => globalRoot s (y x i)
  have hy0 : ∀ i, y ℓ i ≠ 0 := fun i => Complex.exp_ne_zero _
  have hz0 : ∀ i, z ℓ i ≠ 0 := fun i => globalRoot_nonzero s _
  have hzn : ∀ i, ‖z ℓ i‖ < 1 := fun i => interiorRoot_norm_lt_one (hW i)
  have dy : ∀ i, ContDiffAt ℝ ∞ (fun x => y x i) ℓ := by
    intro i
    dsimp [y]
    fun_prop
  have dz : ∀ i, ContDiffAt ℝ ∞ (fun x => z x i) ℓ := by
    intro i
    have dW : ContDiffAt ℝ ∞ (fun x => sourceW s (y x i)) ℓ :=
      contDiffAt_const.sub (((dy i).add ((dy i).inv (hy0 i))).div_const 2)
    exact (interiorRoot_contDiffAt_real (hW i)).comp ℓ dW
  have dY : ContDiffAt ℝ ∞ (fun x => coordinateProduct (y x)) ℓ :=
    contDiffAt_finite_product Finset.univ (fun i x => y x i) ℓ (fun i _ => dy i)
  have dZ : ContDiffAt ℝ ∞ (fun x => coordinateProduct (z x)) ℓ :=
    contDiffAt_finite_product Finset.univ (fun i x => z x i) ℓ (fun i _ => dz i)
  have hY0 : coordinateProduct (y ℓ) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hy0 i)
  have hZ0 : coordinateProduct (z ℓ) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hz0 i)
  have dpair : ContDiffAt ℝ ∞ (fun x => canceledPairProduct (z x) (y x)) ℓ := by
    unfold canceledPairProduct
    apply contDiffAt_finite_product
    intro i _
    apply contDiffAt_finite_product
    intro j _
    exact contDiffAt_quotient (((((dy i).sub (dy j)).pow 2).neg.mul (dz i)).mul (dz j))
      (((dy i).mul (dy j)).mul (((contDiffAt_const (c := (1:ℂ))).sub ((dz i).mul (dz j))).pow 2))
      (mul_ne_zero (mul_ne_zero (hy0 i) (hy0 j))
        (pow_ne_zero 2 (one_sub_mul_ne_zero_of_norm_lt_one (hzn i) (hzn j))))
  have dres : ContDiffAt ℝ ∞ (fun x => ∏ i, residueFactor (z x i)) ℓ := by
    apply contDiffAt_finite_product
    intro i _
    exact contDiffAt_quotient ((contDiffAt_const (c := (2:ℂ))).mul ((dz i).pow 2))
      ((contDiffAt_const (c := (1:ℂ))).sub ((dz i).pow 2))
      (by simpa [pow_two] using one_sub_mul_ne_zero_of_norm_lt_one (hzn i) (hzn i))
  have ddensity : ContDiffAt ℝ ∞ (fun x => onsiteCanceledDensity (z x) (y x)) ℓ :=
    (((dZ.mul dY).inv (mul_ne_zero hZ0 hY0)).mul dpair).mul dres
  exact ((contDiffAt_const.mul dY).mul ddensity)

 theorem onsiteLogDensity_on_source_contDiff {N : ℕ} (hN : 0 < N)
    (f : SelectorFunctions) {r τ lam : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hτ : 0 ≤ τ) (hlam : 0 ≤ lam) (s : ℂ)
    (hmargin : r⁻¹-r < (sourceS s).im)
    (hp0 : ∀ x, 0 ≤ f.p x) (hm0 : ∀ x, 0 ≤ f.m x) (_hm1 : ∀ x, f.m x ≤ 1)
    (hps : ∀ x, Real.sin x ≤ 0 → f.p x=0)
    (hms : ∀ x, 0 ≤ Real.sin x → f.m x=0) (θ : Fin N → ℝ) :
    ContDiffAt ℝ ∞ (onsiteLogDensity N s) (logContour f r τ lam θ) := by
  apply onsiteLogDensity_contDiffAt_real N hN s
  · intro i
    rw [← deformedPoint_exp_log f hr]
    exact (sourceW_upper_of_margin hr hr1 hmargin (deformedPoint_zero_norm f hr.le τ θ i)).trans_le
      (deformed_sourceW_im_ge hN f hr hτ hlam θ s hp0 hm0 hps hms i)


 theorem onsitePulledDensity_joint_contDiffAt {N : ℕ} (hN : 0 < N)
    (f : SelectorFunctions) {r τ lam : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hτ : 0 ≤ τ) (hlam : 0 ≤ lam) (s : ℂ)
    (hmargin : r⁻¹-r < (sourceS s).im)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m)
    (hp0 : ∀ x, 0 ≤ f.p x) (hm0 : ∀ x, 0 ≤ f.m x) (hm1 : ∀ x, f.m x ≤ 1)
    (hps : ∀ x, Real.sin x ≤ 0 → f.p x=0)
    (hms : ∀ x, 0 ≤ Real.sin x → f.m x=0) (θ : Fin N → ℝ) :
    ContDiffAt ℝ ∞ (fun p : ℝ × (Fin N → ℝ) => onsitePulledDensity f r τ p.1 s p.2) (lam,θ) := by
  have hd := (onsiteLogDensity_on_source_contDiff hN f hr hr1 hτ hlam s hmargin hp0 hm0 hm1 hps hms θ).comp
    (lam,θ) (logContour_joint_contDiff f r τ hp hm).contDiffAt
  have hdet := (rowDetContinuous N).contDiff.comp (angularJacobian_joint_contDiff f τ hp hm)
  have hh := hd.mul hdet.contDiffAt
  convert hh using 1
  funext p
  rw [onsitePulledDensity_eq_log f hr]
  rfl

 theorem onsiteHomotopyFlux_joint_contDiffAt {N : ℕ} (hN : 0 < N)
    (f : SelectorFunctions) {r τ lam : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hτ : 0 ≤ τ) (hlam : 0 ≤ lam) (s : ℂ)
    (hmargin : r⁻¹-r < (sourceS s).im)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m)
    (hp0 : ∀ x, 0 ≤ f.p x) (hm0 : ∀ x, 0 ≤ f.m x) (hm1 : ∀ x, f.m x ≤ 1)
    (hps : ∀ x, Real.sin x ≤ 0 → f.p x=0)
    (hms : ∀ x, 0 ≤ Real.sin x → f.m x=0) (θ : Fin N → ℝ) (q : Fin N) :
    ContDiffAt ℝ ∞ (fun p : ℝ × (Fin N → ℝ) => onsiteHomotopyFlux f r τ p.1 s p.2 q) (lam,θ) := by
  have hd := (onsiteLogDensity_on_source_contDiff hN f hr hr1 hτ hlam s hmargin hp0 hm0 hm1 hps hms θ).comp
    (lam,θ) (logContour_joint_contDiff f r τ hp hm).contDiffAt
  have hM := angularJacobian_joint_contDiff (N := N) f τ hp hm
  have hv : ContDiff ℝ ∞ (fun p : ℝ × (Fin N → ℝ) => complexShift f τ p.2) := by
    have ho : ContDiff ℝ ∞ Complex.ofReal := Complex.ofRealCLM.contDiff
    apply contDiff_pi.mpr
    intro i
    unfold complexShift shiftMap retractionShift occupancy
    fun_prop
  have hc : ContDiff ℝ ∞ (fun (p : ℝ × (Fin N → ℝ)) i j =>
      (angularJacobian f τ p.1 p.2).updateCol q (complexShift f τ p.2) i j) := by
    apply contDiff_pi.mpr
    intro i
    apply contDiff_pi.mpr
    intro j
    simp only [Matrix.updateCol_apply]
    by_cases hj : j=q
    · simp only [hj,ite_true]
      exact (contDiff_apply ℝ ℂ i).comp hv
    · simp only [hj,ite_false]
      exact (contDiff_apply ℝ ℂ j).comp ((contDiff_apply ℝ (Fin N → ℂ) i).comp hM)
  exact hd.mul ((rowDetContinuous N).contDiff.comp hc).contDiffAt

end
end IsingBulk.HT.Contour
