import IsingBulk.HT22.Physical.Symmetries
import IsingBulk.First.RegularShapeSource
import IsingBulk.Tail.SelectorOriginal

/-! Exact F001 lower angular chart: actual physical small roots and all
normalization factors, before invoking any limiting theorem. -/
namespace IsingBulk.HT22.LocalLimit
noncomputable section
open Complex Set MeasureTheory Filter Metric IsingBulk.First IsingBulk.Tail
open scoped BigOperators Topology

def lowerChartAngles {n : ℕ} (α : ℝ) (u : Fin n → ℝ) : Fin (n+1) → ℝ :=
  fun j => shapeExtend u j-α

theorem lowerChart_shapeY {n : ℕ} (α : ℝ) (u : Fin n → ℝ) :
    shapeY α u = fun j => IsingBulk.Tail.limitingAngle (lowerChartAngles α u j) := by
  funext j
  unfold shapeY lowerChartAngles IsingBulk.Tail.limitingAngle
  rw [ofReal_sub]

theorem angularRoot_eq_phaseRoot {s : ℂ} (hs : 1<‖s‖) (θ : ℝ)
    (hi : 0<(sourceS s).im) :
    Physical.angularRoot s θ = phaseRoot (sourceW s (IsingBulk.Tail.limitingAngle θ)) := by
  apply Eq.symm
  apply IsingBulk.First.Regular.phaseRoot_eq_interior_root_of_upper
  · unfold Physical.angularRoot
    rw [Physical.angularW_eq_sourceW]
    exact IsingBulk.Preferred22.physicalRoot_quadratic _
  · exact Physical.angularRoot_norm_lt_one hs θ
  · rw [sourceW,IsingBulk.Tail.limitingAngle_trace]
    simpa only [sub_im,div_ofNat_im,mul_im,ofReal_im,ofReal_re,im_ofNat,re_ofNat,
      mul_zero,zero_mul,add_zero,zero_div,sub_zero] using hi

theorem lowerChart_shapeZ {n : ℕ} {s : ℂ} (hs : 1<‖s‖)
    (hi : 0<(sourceS s).im) (α : ℝ) (u : Fin n → ℝ) :
    shapeZ s α u = fun j => Physical.angularRoot s (lowerChartAngles α u j) := by
  funext j
  unfold shapeZ
  rw [lowerChart_shapeY]
  exact (angularRoot_eq_phaseRoot hs _ hi).symm

/-- The post-mean source is *literally* the new constrained angular density
on this chart, with free-coordinate normalized measure `(2pi)^(-n)`.
No parity or old first-singularity conclusion is used. -/
theorem postMeanDensity_eq_angular {n : ℕ} {s : ℂ} (hs : 1<‖s‖)
    (hi : 0<(sourceS s).im) (α : ℝ) (u : Fin n → ℝ)
    (ha : exp (-(n+1:ℂ)*(α:ℂ)*I)=1)
    (hy : ∀ i j : Fin (n+1), 1-shapeY α u i*shapeY α u j≠0) :
    postMeanDensity s α u = ((2*(Real.pi:ℂ))^n)⁻¹ *
      Physical.signedAngularDensity false s (lowerChartAngles α u) := by
  let z := shapeZ s α u
  let y := shapeY α u
  have hz : ∀ i, z i≠0 := fun i => phaseRoot_ne_zero _
  have hy0 : ∀ i, y i≠0 := fun i => exp_ne_zero _
  have hzn : ∀ i, ‖z i‖<1 := by
    intro i
    dsimp [z]
    rw [lowerChart_shapeZ hs hi]
    exact Physical.angularRoot_norm_lt_one hs _
  have hzgap : ∀ i j,1-z i*z j≠0 := fun i j =>
    one_sub_mul_ne_zero_of_norm_lt_one (hzn i) (hzn j)
  have hpairs := canceledPairProduct_eq s z y hy0 hz
    (shapeZ_source_quadratic s α u) hy hzgap
  have hY : ∏ j,y j=1 := coordinateProduct_shapeY α u ha
  have hZ : (∏ j,z j)≠0 := Finset.prod_ne_zero_iff.mpr (fun j _ => hz j)
  have hpi : 2*(Real.pi:ℂ)≠0 := by exact_mod_cast (show 2*Real.pi≠0 by positivity)
  have hres : (∏ j,residueFactor (z j))=(∏ j,z j)*(∏ j,Physical.oneBody (z j)) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j _
    rw [residueFactor,Physical.oneBody_eq_rational]
    ring
  have hmeasure : (∏ j,y j/(2*(Real.pi:ℂ)))=((2*(Real.pi:ℂ))^(n+1))⁻¹ := by
    rw [Finset.prod_div_distrib,hY]
    simp
  have hden : 1-∏ j,z j≠0 := by
    simpa only [one_mul,coordinateProduct] using IsingBulk.HT.Contour.signed_product_gap_ne_zero
      (Nat.succ_pos n) 1 (by norm_num) z hzn
  unfold postMeanDensity shapeRegularNumerator shapePoleDenominator shapeZProduct coordinateProduct
  change 2*(Real.pi:ℂ)*(((∏ j,z j)⁻¹+1)*pairProduct z*pairProduct y*
      (∏ j,residueFactor (z j))*(∏ j,y j/(2*(Real.pi:ℂ))))/(1-∏ j,z j)=_
  rw [hres,hmeasure]
  unfold Physical.signedAngularDensity
  simp only [Physical.constraintSign,Bool.false_eq_true,↓reduceIte,one_mul]
  have hzEq (j : Fin (n+1)) : Physical.angularRoot s (lowerChartAngles α u j)=z j :=
    (congrFun (lowerChart_shapeZ hs hi α u) j).symm
  have hyEq (j : Fin (n+1)) : limitingAngle (lowerChartAngles α u j)=y j :=
    (congrFun (lowerChart_shapeY α u) j).symm
  simp_rw [hzEq,hyEq]
  change _ = ((2*(Real.pi:ℂ))^n)⁻¹*
    ((1+∏ j,z j)/(1-∏ j,z j)*(∏ j,Physical.oneBody (z j))*canceledPairProduct z y)
  rw [hpairs,pow_succ]
  field_simp

/-- The centered chart obeys the actual dependent-angle constraint modulo the
prime resonance, with no dropped site or extra angle integral. -/
theorem constrainedDensity_lowerChart {n : ℕ} (s : ℂ) (α : ℝ) (u : Fin n → ℝ)
    (ha : exp (-(n+1:ℂ)*(α:ℂ)*I)=1) :
    Physical.signedAngularDensity false s
      (Physical.constrainedAngles false n (fun i => u i-α)) =
      Physical.signedAngularDensity false s (lowerChartAngles α u) := by
  have hpos : exp ((n+1:ℂ)*(α:ℂ)*I)=1 := by
    have hh := congrArg Inv.inv ha
    rw [← exp_neg] at hh
    rw [inv_one] at hh
    convert hh using 1
    congr 1
    ring
  apply Physical.signedAngularDensity_congr_angles
  intro j
  rw [← Physical.limitingAngle_eq_preferred,← Physical.limitingAngle_eq_preferred]
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp only [Physical.constrainedAngles,Physical.constraintAngle,Bool.false_eq_true,
      ↓reduceIte,Fin.snoc_last,lowerChartAngles,shapeExtend_last,
      Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    calc
      limitingAngle (0-((∑ i,u i)-(n:ℝ)*α)) =
          exp ((n+1:ℂ)*(α:ℂ)*I)*limitingAngle (-(∑ i,u i)-α) := by
        unfold limitingAngle
        rw [← exp_add]
        congr 1
        push_cast
        ring
      _ = _ := by rw [hpos,one_mul]
  · simp only [Physical.constrainedAngles,Fin.snoc_castSucc,lowerChartAngles,shapeExtend_castSucc]

/-- Raw reflection identifies the two charts exactly, without conjugating s. -/
theorem lower_upper_density_equal {n : ℕ} (s : ℂ) (α : ℝ) (u : Fin n → ℝ) :
    Physical.signedAngularDensity false s (fun j => -lowerChartAngles α u j) =
      Physical.signedAngularDensity false s (lowerChartAngles α u) :=
  Physical.signedAngularDensity_reflect false s _

end
end IsingBulk.HT22.LocalLimit
