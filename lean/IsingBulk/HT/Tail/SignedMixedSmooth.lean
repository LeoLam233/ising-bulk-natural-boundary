import IsingBulk.HT.Tail.SignedCompactSource
import IsingBulk.Tail.MixedKernelTransport

namespace IsingBulk.HT.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Tail IsingBulk.Lie IsingBulk.HT.Contour Set Filter
open scoped Topology ContDiff BigOperators
set_option backward.isDefEq.respectTransparency false

theorem signedPulledDensity_zero_independent (ζ : ℂ) {N : ℕ} (f g : SelectorFunctions)
    (r τ : ℝ) (s : ℂ) (θ : Fin N → ℝ) :
    signedPulledDensity ζ f r τ 0 s θ = signedPulledDensity ζ g r τ 0 s θ := by
  simp only [signedPulledDensity,deformedPoint_zero,angularJacobian_zero]

theorem mixedSeparated_regularDensity_smooth {N : ℕ} (_hN : 0 < N)
    (J : Finset (Fin N)) (j q : Fin N) (f : SelectorFunctions) {r : ℝ}
    (hr : 0 < r) (τ lam : ℝ) (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m) :
    ParameterSmoothOn (mixedSeparatedDomain J j q f r τ lam) (compactRegularDensity f r τ lam) := by
  let Ω := mixedSeparatedDomain J j q f r τ lam
  let y := fun (_ : ℂ) (θ : Fin N → ℝ) (i : Fin N) => deformedPoint f r τ lam θ i
  let z := fun s θ i => globalRoot s (y s θ i)
  have hy (i : Fin N) : ParameterSmoothOn Ω (fun s θ => y s θ i) := mixedSeparated_y_smooth J j q f r τ lam hp hm i
  have hz (i : Fin N) : ParameterSmoothOn Ω (fun s θ => z s θ i) := mixedSeparated_root_smooth J j q f hr τ lam hp hm i
  have hyn (p : ℂ × (Fin N → ℝ)) : ∀ i,y p.1 p.2 i ≠ 0 := deformedPoint_nonzero f hr.ne' τ lam p.2
  have hzn (p : ℂ × (Fin N → ℝ)) : ∀ i,z p.1 p.2 i ≠ 0 := fun i => globalRoot_nonzero _ _
  have hnorm (p : ℂ × (Fin N → ℝ)) (h : p ∈ Ω) (i : Fin N) : ‖z p.1 p.2 i‖ < 1 :=
    interiorRoot_norm_lt_one (h.2.1 i)
  have hY := mixedSeparated_Y_smooth J j q f r τ lam hp hm
  have hZ := mixedSeparated_Z_smooth J j q f hr τ lam hp hm
  have hYn (p : ℂ × (Fin N → ℝ)) : coordinateProduct (y p.1 p.2) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => hyn p i)
  have hZn (p : ℂ × (Fin N → ℝ)) : coordinateProduct (z p.1 p.2) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => hzn p i)
  have hpair (i k : Fin N) : ParameterSmoothOn Ω
      (fun s θ => canceledPair (y s θ i) (y s θ k) (z s θ i) (z s θ k)) := by
    have hn' := (((ParameterSmoothOn.const Ω (-1)).mul (((hy i).sub (hy k)).pow 2)).mul (hz i)).mul (hz k)
    have hd := ((hy i).mul (hy k)).mul (((ParameterSmoothOn.const Ω 1).sub ((hz i).mul (hz k))).pow 2)
    simpa only [canceledPair,neg_one_mul] using hn'.div hd (fun p h =>
      mul_ne_zero (mul_ne_zero (hyn p i) (hyn p k))
        (pow_ne_zero 2 (one_sub_mul_ne_zero_of_norm_lt_one (hnorm p h i) (hnorm p h k))))
  have hPairs : ParameterSmoothOn Ω (fun s θ => canceledPairProduct (z s θ) (y s θ)) :=
    ParameterSmoothOn.prod Finset.univ _ (fun i _ => ParameterSmoothOn.prod _ _ (fun k _ => hpair i k))
  have hres (i : Fin N) : ParameterSmoothOn Ω (fun s θ => residueFactor (z s θ i)) :=
    ((ParameterSmoothOn.const Ω 2).mul ((hz i).pow 2)).div
      ((ParameterSmoothOn.const Ω 1).sub ((hz i).pow 2))
      (fun p h => by simpa only [pow_two] using one_sub_mul_ne_zero_of_norm_lt_one (hnorm p h i) (hnorm p h i))
  have hOneBody := ParameterSmoothOn.prod Finset.univ _ (fun i _ => (hy i).mul (hres i))
  have hdetAngular : ContDiff ℝ ∞ (fun θ : Fin N → ℝ => (angularJacobian f τ lam θ).det) :=
    ((rowDetContinuous N).contDiff.comp (angularJacobian_joint_contDiff f τ hp hm)).comp
      (contDiff_const.prodMk contDiff_id)
  have hNorm : ParameterSmoothOn Ω (fun _ θ => mixedDensityNormalization f τ lam θ) :=
    ((ParameterSmoothOn.const Ω (N.factorial:ℂ)⁻¹).mul
      (ParameterSmoothOn.const Ω ((2*(Real.pi:ℂ)*Complex.I)^(-(N:ℤ))))).mul
        (ParameterSmoothOn.angular Ω _ hdetAngular)
  exact ((hNorm.mul ((hZ.inv (fun p _ => hZn p)).add (hY.inv (fun p _ => hYn p)))).mul hPairs).mul hOneBody

theorem signed_mixedSeparated_kernel_smooth (σ : ℂ) (hσ : ‖σ‖ = 1)
    {N : ℕ} (hN : 0 < N) (J : Finset (Fin N)) (j q : Fin N)
    (f : SelectorFunctions) {r : ℝ} (hr : 0 < r) (τ lam : ℝ)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m)
    (hY : ∀ θ : Fin N → ℝ, ‖coordinateProduct (deformedPoint f r τ lam θ)‖ < 1) :
    ParameterSmoothOn (mixedSeparatedDomain J j q f r τ lam)
      (signedMixedSimpleKernel σ f r τ lam) := by
  let Ω := mixedSeparatedDomain J j q f r τ lam
  have hYs := (ParameterSmoothOn.const Ω σ).mul (mixedSeparated_Y_smooth J j q f r τ lam hp hm)
  have hZs := (ParameterSmoothOn.const Ω σ).mul (mixedSeparated_Z_smooth J j q f hr τ lam hp hm)
  exact (((ParameterSmoothOn.const Ω 1).sub hZs).inv (fun p h =>
    signed_product_gap_ne_zero hN σ hσ _ (fun i => interiorRoot_norm_lt_one (h.2.1 i)))).mul
    (((ParameterSmoothOn.const Ω 1).sub hYs).inv (fun p _ => signed_gap_ne_zero σ _ hσ (hY p.2)))

theorem signed_mixedSeparated_density_smooth (σ : ℂ) (hσ : ‖σ‖ = 1)
    {N : ℕ} (hN : 0 < N) (J : Finset (Fin N)) (j q : Fin N)
    (f : SelectorFunctions) {r : ℝ} (hr : 0 < r) (τ lam : ℝ)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m)
    (hY : ∀ θ : Fin N → ℝ, ‖coordinateProduct (deformedPoint f r τ lam θ)‖ < 1) :
    ParameterSmoothOn (mixedSeparatedDomain J j q f r τ lam)
      (signedPulledDensity σ f r τ lam) := by
  apply ((signed_mixedSeparated_kernel_smooth σ hσ hN J j q f hr τ lam hp hm hY).mul
    (mixedSeparated_regularDensity_smooth hN J j q f hr τ lam hp hm)).congr
    (mixedSeparatedDomain_isOpen J j q f hr τ lam hp hm)
  intro p _
  exact signed_compact_pulledDensity_factorization σ f r τ lam p.1 p.2

end
end IsingBulk.HT.Tail
