import IsingBulk.Tail.MixedSeparatedVelocity

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set Filter
open scoped Topology ContDiff BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

theorem interiorRoot_analyticAt_upper_parameter {W : ℂ} (hW : 0<W.im) :
    AnalyticAt ℂ interiorRoot W := by
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  filter_upwards [Complex.continuous_im.continuousAt.eventually (Ioi_mem_nhds hW)] with w hw
  exact interiorRoot_differentiableAt hw

theorem mixedSeparated_root_smooth {N : ℕ} (J : Finset (Fin N)) (j q : Fin N)
    (f : SelectorFunctions) {r : ℝ} (hr : 0<r) (τ lam : ℝ)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m) (i : Fin N) :
    ParameterSmoothOn (mixedSeparatedDomain J j q f r τ lam)
      (fun s θ => globalRoot s (deformedPoint f r τ lam θ i)) :=
  (mixedSeparated_W_smooth J j q f hr τ lam hp hm i).complex_comp interiorRoot
    (fun _ h => interiorRoot_analyticAt_upper_parameter (h.2.1 i))

theorem mixedSeparated_density_smooth {N : ℕ} (hN : 0<N) (J : Finset (Fin N)) (j q : Fin N)
    (f : SelectorFunctions) {r : ℝ} (hr : 0<r) (τ lam : ℝ)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m) :
    ParameterSmoothOn (mixedSeparatedDomain J j q f r τ lam) (pulledDensity f r τ lam) := by
  let Ω := mixedSeparatedDomain J j q f r τ lam
  let y := fun (_ : ℂ) (θ : Fin N → ℝ) (i : Fin N) => deformedPoint f r τ lam θ i
  let z := fun s θ i => globalRoot s (y s θ i)
  have hy (i : Fin N) : ParameterSmoothOn Ω (fun s θ => y s θ i) := mixedSeparated_y_smooth J j q f r τ lam hp hm i
  have hz (i : Fin N) : ParameterSmoothOn Ω (fun s θ => z s θ i) := mixedSeparated_root_smooth J j q f hr τ lam hp hm i
  have hyn (p : ℂ × (Fin N → ℝ)) : ∀ i,y p.1 p.2 i≠0 := deformedPoint_nonzero f hr.ne' τ lam p.2
  have hzn (p : ℂ × (Fin N → ℝ)) : ∀ i,z p.1 p.2 i≠0 := fun i => globalRoot_nonzero _ _
  have hnorm (p : ℂ × (Fin N → ℝ)) (h : p∈Ω) (i : Fin N) : ‖z p.1 p.2 i‖<1 := interiorRoot_norm_lt_one (h.2.1 i)
  have hY : ParameterSmoothOn Ω (fun s θ => coordinateProduct (y s θ)) := ParameterSmoothOn.prod Finset.univ _ (fun i _ => hy i)
  have hZ : ParameterSmoothOn Ω (fun s θ => coordinateProduct (z s θ)) := ParameterSmoothOn.prod Finset.univ _ (fun i _ => hz i)
  have hYn (p : ℂ × (Fin N → ℝ)) : coordinateProduct (y p.1 p.2)≠0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hyn p i)
  have hZn (p : ℂ × (Fin N → ℝ)) : coordinateProduct (z p.1 p.2)≠0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hzn p i)
  have hZgap (p : ℂ × (Fin N → ℝ)) (h : p∈Ω) : 1-coordinateProduct (z p.1 p.2)≠0 := one_sub_coordinateProduct_ne_zero hN (hnorm p h)
  have hpair (i k : Fin N) : ParameterSmoothOn Ω (fun s θ => canceledPair (y s θ i) (y s θ k) (z s θ i) (z s θ k)) := by
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
  have hResidues := ParameterSmoothOn.prod Finset.univ _ (fun i _ => hres i)
  have hReduced : ParameterSmoothOn Ω (fun s θ => canceledReducedDensity (z s θ) (y s θ)) :=
    ((((hZ.inv (fun p _ => hZn p)).add (hY.inv (fun p _ => hYn p))).div
      (((ParameterSmoothOn.const Ω 1).sub hZ).mul ((ParameterSmoothOn.const Ω 1).sub hY))
      (fun p h => mul_ne_zero (hZgap p h) h.2.2.2.2)).mul hPairs).mul hResidues
  have hdetAngular : ContDiff ℝ ∞ (fun θ : Fin N → ℝ => (angularJacobian f τ lam θ).det) :=
    ((rowDetContinuous N).contDiff.comp (angularJacobian_joint_contDiff f τ hp hm)).comp
      (contDiff_const.prodMk contDiff_id)
  have hdet := ParameterSmoothOn.angular Ω _ hdetAngular
  exact ((((ParameterSmoothOn.const Ω (N.factorial:ℂ)⁻¹).mul
    (ParameterSmoothOn.const Ω ((2*(Real.pi:ℂ)*Complex.I)^(-(N:ℤ))))).mul hdet).mul hY).mul hReduced

end
end IsingBulk.Tail
