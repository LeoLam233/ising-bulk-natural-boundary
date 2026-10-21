import IsingBulk.HT.Contour.SignedChartBridge
import IsingBulk.HT.Contour.SignedContinuation
import IsingBulk.First.SymmetryIntegral

/-! Exact negative-upper physical attachment. The interior quadratic root,
normalized circle orientation, factorial and angular Jacobian are all retained.
This proves an auxiliary signed-integral identity, not HT susceptibility evenness. -/
namespace IsingBulk.HT.Contour
noncomputable section
open IsingBulk.First IsingBulk.Tail Set MeasureTheory
open scoped BigOperators
set_option maxHeartbeats 1000000

@[simp] theorem sourceS_neg_conjugate_im (s : ℂ) :
    (sourceS (-star s)).im = (sourceS s).im := by
  rw [sourceS_neg,sourceS_conjugate]
  simp

/-- The same admissible radius and the strict interior-root uniqueness fix
which branch occurs under reflection of the upper half-plane. -/
theorem globalRoot_neg_conjugate_on_circle {r : ℝ} {s y : ℂ}
    (hr : 0 < r) (hr1 : r < 1) (hm : r⁻¹-r < (sourceS s).im)
    (hy : ‖y‖ = r) :
    globalRoot (-star s) (-star y) = -star (globalRoot s y) := by
  have h := globalRoot_admissible hr hr1 hm
  have hm' : r⁻¹-r < (sourceS (-star s)).im := by
    rw [sourceS_neg_conjugate_im]
    exact hm
  have h' := globalRoot_admissible hr hr1 hm'
  have ht : ScalarResidueAdmissible r (-star s)
      (fun v => -star (globalRoot s (-star v))) := by
    simpa only [star_neg] using h.conjugate.neg
  have hyr : ‖-star y‖ = r := by simpa using hy
  have he := quadratic_root_unique
    (residue_quadratic_eq (h'.root_quadratic (-star y) hyr))
    (residue_quadratic_eq (ht.root_quadratic (-star y) hyr))
    ((h'.root_inside (-star y) hyr).trans hr1)
    ((ht.root_inside (-star y) hyr).trans hr1)
  simpa only [star_neg,star_star,neg_neg] using he

 theorem canceledPair_neg_conjugate (a b z w : ℂ) :
    canceledPair (-star a) (-star b) (-star z) (-star w) =
      star (canceledPair a b z w) := by
  unfold canceledPair
  simp only [star_div₀,star_mul',star_neg,star_pow,star_sub,star_one]
  ring

 theorem canceledPairProduct_neg_conjugate {N : ℕ} (z y : Fin N → ℂ) :
    canceledPairProduct (fun i => -star (z i)) (fun i => -star (y i)) =
      star (canceledPairProduct z y) := by
  simp only [canceledPairProduct,canceledPair_neg_conjugate,star_prod]

 theorem coordinateProduct_neg_conjugate_odd {N : ℕ} (hN : Odd N) (y : Fin N → ℂ) :
    coordinateProduct (fun i => -star (y i)) = -star (coordinateProduct y) := by
  simp only [coordinateProduct,Finset.prod_neg,Finset.card_univ,Fintype.card_fin,
    hN.neg_one_pow,neg_one_mul,star_prod]

 theorem signedCanceledDensity_reflect_odd {N : ℕ} (hN : Odd N) (z y : Fin N → ℂ) :
    signedCanceledDensity 1 (fun i => -star (z i)) (fun i => -star (y i)) =
      -star (signedCanceledDensity (-1) z y) := by
  have hr (i : Fin N) : residueFactor (-star (z i)) = star (residueFactor (z i)) := by
    simp [residueFactor]
  unfold signedCanceledDensity
  rw [coordinateProduct_neg_conjugate_odd hN,coordinateProduct_neg_conjugate_odd hN,
    canceledPairProduct_neg_conjugate]
  simp_rw [hr]
  simp only [signedGlobalFactor,one_mul,neg_one_mul,inv_neg,star_mul',star_div₀,
    star_inv₀,star_add,star_sub,star_neg,star_one,star_prod]
  ring

/-- Literal signed angular source continuity, obtained by composing the actual
continued density on its root-and-signed-gap domain. -/
theorem signedSourceAngularDensity_continuous (σ : ℂ) (hσ : ‖σ‖ = 1)
    (N : ℕ) (hN : 0 < N) {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    {s : ℂ} (hm : r⁻¹-r < (sourceS s).im) :
    Continuous (signedSourceAngularDensity (N := N) σ r s) := by
  have hs : s ≠ 0 := (dampingDomain_of_margin hr hr1 hm).1
  have hup (x : Fin N → ℝ) (i : Fin N) :
      0 < (sourceW s (angleTuple r x i)).im :=
    sourceW_upper_of_margin hr hr1 hm (anglePoint_norm hr.le _)
  have he (x : Fin N → ℝ) (i : Fin N) :
      selectedContinuedRoot s (angleTuple r x i) = globalRoot s (angleTuple r x i) :=
    continuedRoot_eq_interiorRoot (hup x i)
  have ha (x : Fin N → ℝ) : AnalyticAt ℂ (signedContinuedContourDensity σ N) (s,angleTuple r x) := by
    apply signed_continuedContourDensity_analyticAt σ hs
    · intro i
      exact norm_ne_zero_iff.mp ((anglePoint_norm hr.le (x i)).trans_ne hr.ne')
    · intro i
      exact Or.inl (Or.inl (hup x i))
    · apply signed_product_gap_ne_zero hN σ hσ
      intro i
      exact (anglePoint_norm hr.le (x i)).trans_lt hr1
    · apply signed_product_gap_ne_zero hN σ hσ
      intro i
      rw [he]
      exact interiorRoot_norm_lt_one (hup x i)
  have hc : Continuous (fun x : Fin N → ℝ => signedContinuedContourDensity σ N (s,angleTuple r x)) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (ha x).continuousAt.comp (f := fun x : Fin N → ℝ => (s,angleTuple r x))
      ((continuous_const.prodMk (angleTuple_continuous r)).continuousAt)
  have hpoint : signedSourceAngularDensity (N := N) σ r s =
      (fun x => ((2*(Real.pi:ℂ))⁻¹)^N*signedContinuedContourDensity σ N (s,angleTuple r x)) := by
    funext x
    unfold signedSourceAngularDensity signedContinuedContourDensity angleProductJacobian angleJacobian
    simp_rw [he]
    simp only [angleTuple,div_eq_mul_inv,Finset.prod_mul_distrib,Finset.prod_const,
      Finset.card_univ,Fintype.card_fin]
    ring
  rw [hpoint]
  exact continuous_const.mul hc

/-- The signed physical integral is exactly its normalized iterated contour,
with no assumed Fubini or normalizing constant. -/
theorem signedSourceIntegral_eq_multiCircle (σ : ℂ) (hσ : ‖σ‖ = 1)
    (N : ℕ) (hN : 0 < N) {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    {s : ℂ} (hm : r⁻¹-r < (sourceS s).im) :
    signedSourceIntegral σ N r s = (N.factorial:ℂ)⁻¹ *
      multiCircleIntegral r N (fun y => signedCanceledDensity σ (fun i => globalRoot s (y i)) y) := by
  rw [signedSourceIntegral_eq_angular,multiCircleIntegral_eq_angle]
  change (N.factorial:ℂ)⁻¹ * (∫ x in angleBox N,signedSourceAngularDensity σ r s x) =
    (N.factorial:ℂ)⁻¹ * multiAngleIntegral N (signedSourceAngularDensity σ r s)
  rw [multiAngleIntegral_eq_box N _
    (signedSourceAngularDensity_continuous σ hσ N hN hr hr1 hm)]

/-- Exact normalized multi-circle reflection. It includes orientation, even
for odd-dimensional contours, without an integrability assumption. -/
theorem multiCircleIntegral_neg_conjugate (r : ℝ) (N : ℕ)
    (F : (Fin N → ℂ) → ℂ) :
    multiCircleIntegral r N (fun y => star (F (fun i => -star (y i)))) =
      (-1:ℂ)^N*star (multiCircleIntegral r N F) := by
  have h := multiCircleIntegral_conjugate r N (fun y => F (fun i => -y i))
  rw [multiCircleIntegral_neg,star_mul'] at h
  simpa only [star_pow,star_neg,star_one] using h

/-- The actual odd negative-upper form factor is the conjugate of the
negative-sign source at the reflected acute parameter. -/
theorem upperFormFactor_reflected_odd_eq_signed (N : ℕ) (hN : Odd N)
    (hNpos : 0 < N) (f : SelectorFunctions) (r τ : ℝ) (s : ℂ)
    (hr : 0 < r) (hr1 : r < 1) (hm : r⁻¹-r < (sourceS s).im) :
    upperFormFactor N (-star s) = star (signedSourceIntegral (-1) N r s) := by
  have hm' : r⁻¹-r < (sourceS (-star s)).im := by
    rw [sourceS_neg_conjugate_im]
    exact hm
  rw [← signedSourceIntegral_one_eq_upper N hNpos f r τ (-star s) hr hr1 hm',
    signedSourceIntegral_eq_multiCircle 1 (by simp) N hNpos hr hr1 hm',
    signedSourceIntegral_eq_multiCircle (-1) (by simp) N hNpos hr hr1 hm,
    star_mul']
  simp only [star_inv₀,star_natCast]
  congr 1
  let F : (Fin N → ℂ) → ℂ := fun y =>
    signedCanceledDensity (-1) (fun i => globalRoot s (y i)) y
  change multiCircleIntegral r N (fun y => signedCanceledDensity 1
    (fun i => globalRoot (-star s) (y i)) y) = star (multiCircleIntegral r N F)
  have hp : multiCircleIntegral r N (fun y => signedCanceledDensity 1
      (fun i => globalRoot (-star s) (y i)) y) =
      multiCircleIntegral r N (fun y => -star (F (fun i => -star (y i)))) := by
    apply multiCircleIntegral_congr hr.le N
    intro y hy
    have hy' (i : Fin N) : ‖-star (y i)‖ = r := by simpa using hy i
    have he (i : Fin N) : globalRoot (-star s) (y i) = -star (globalRoot s (-star (y i))) := by
      simpa only [star_neg,star_star,neg_neg] using globalRoot_neg_conjugate_on_circle hr hr1 hm (hy' i)
    have hyback : (fun i => -star (-star (y i))) = y := by funext i; simp
    have hz : (fun i => globalRoot (-star s) (y i)) =
        (fun i => -star (globalRoot s (-star (y i)))) := funext he
    rw [hz]
    have hh := signedCanceledDensity_reflect_odd hN (fun i => globalRoot s (-star (y i)))
      (fun i => -star (y i))
    simpa only [hyback,F] using hh
  rw [hp]
  have hn : (fun y : Fin N → ℂ => -star (F (fun i => -star (y i)))) =
      (fun y => (-1:ℂ)*star (F (fun i => -star (y i)))) := by funext y; ring
  rw [hn,multiCircleIntegral_const_mul,multiCircleIntegral_neg_conjugate,hN.neg_one_pow]
  ring

end
end IsingBulk.HT.Contour
