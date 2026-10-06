import IsingBulk.Tail.CompactSelectedField

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First Set
open scoped Topology ContDiff BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def compactRegularDensity {N : ℕ} (f : SelectorFunctions) (r τ lam : ℝ)
    (s : ℂ) (θ : Fin N → ℝ) : ℂ :=
  let y := deformedPoint f r τ lam θ
  let z := fun i => globalRoot s (y i)
  mixedDensityNormalization f τ lam θ*
    ((coordinateProduct z)⁻¹+(coordinateProduct y)⁻¹)*canceledPairProduct z y*
      ∏ i,y i*residueFactor (z i)

theorem compact_pulledDensity_factorization {N : ℕ} (f : SelectorFunctions)
    (r τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ) :
    pulledDensity f r τ lam s θ=mixedSimpleKernel f r τ lam s θ*compactRegularDensity f r τ lam s θ := by
  unfold pulledDensity canceledReducedDensity mixedSimpleKernel compactRegularDensity mixedDensityNormalization
  simp only [Finset.prod_mul_distrib,div_eq_mul_inv,mul_inv_rev]
  ring

theorem compactRegularDensity_smooth {N : ℕ} (hN : 0 < N)
    (f : SelectorFunctions) (hf : RegularSelector f) {r τ lam : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ) (hlam : 0 ≤ lam) :
    ParameterSmoothOn (compactSourceDomain N r) (compactRegularDensity f r τ lam) := by
  let Ω := compactSourceDomain N r
  let y := fun (_ : ℂ) (θ : Fin N → ℝ) (i : Fin N) => deformedPoint f r τ lam θ i
  let z := fun s θ i => globalRoot s (y s θ i)
  have hy (i : Fin N) : ParameterSmoothOn Ω (fun s θ => y s θ i) := compactSource_y_smooth f hf r τ lam i
  have hz (i : Fin N) : ParameterSmoothOn Ω (fun s θ => z s θ i) := compactSource_root_smooth hN f hf hr hr1 hτ hlam i
  have hyn (p : ℂ × (Fin N → ℝ)) : ∀ i,y p.1 p.2 i ≠ 0 := deformedPoint_nonzero f hr.ne' τ lam p.2
  have hzn (p : ℂ × (Fin N → ℝ)) : ∀ i,z p.1 p.2 i ≠ 0 := fun i => globalRoot_nonzero _ _
  have hnorm (p : ℂ × (Fin N → ℝ)) (h : p ∈ Ω) (i : Fin N) : ‖z p.1 p.2 i‖ < 1 :=
    interiorRoot_norm_lt_one (deformed_sourceW_upper_on_damping hN f hf hr hr1 hτ hlam h.1 p.2 i)
  have hY := compactSource_Y_smooth (N := N) f hf r τ lam
  have hZ := compactSource_Z_smooth hN f hf hr hr1 hτ hlam
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
    ((rowDetContinuous N).contDiff.comp (angularJacobian_joint_contDiff f τ hf.p_smooth hf.m_smooth)).comp
      (contDiff_const.prodMk contDiff_id)
  have hNorm : ParameterSmoothOn Ω (fun _ θ => mixedDensityNormalization f τ lam θ) :=
    ((ParameterSmoothOn.const Ω (N.factorial:ℂ)⁻¹).mul
      (ParameterSmoothOn.const Ω ((2*(Real.pi:ℂ)*Complex.I)^(-(N:ℤ))))).mul
        (ParameterSmoothOn.angular Ω _ hdetAngular)
  exact ((hNorm.mul ((hZ.inv (fun p _ => hZn p)).add (hY.inv (fun p _ => hYn p)))).mul hPairs).mul hOneBody

theorem compactSource_density_smooth {N : ℕ} (hN : 0 < N)
    (f : SelectorFunctions) (hf : RegularSelector f) {r τ lam : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ) (hlam : 0 ≤ lam) :
    ParameterSmoothOn (compactSourceDomain N r) (pulledDensity f r τ lam) := by
  apply ((compactSource_kernel_smooth hN f hf hr hr1 hτ hlam).mul
    (compactRegularDensity_smooth hN f hf hr hr1 hτ hlam)).congr (compactSourceDomain_isOpen N r)
  intro p _
  exact compact_pulledDensity_factorization f r τ lam p.1 p.2

end
end IsingBulk.Tail
