import IsingBulk.HT.Contour.OnsiteRetraction
import IsingBulk.HT.Contour.OnsiteDensityEstimate
import IsingBulk.HT.Final.UpperOnsiteRadius
import IsingBulk.First.SymmetryIntegral

/-! Exact onsite source attachment to the double contour and its canonical
upper representative, including normalization and every fixed-radius jet. -/
namespace IsingBulk.HT.Contour
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.HT.Final Set MeasureTheory Filter
open scoped BigOperators Topology

def onsiteSourceAngularDensity {N : ℕ} (r : ℝ) (s : ℂ) (x : Fin N → ℝ) : ℂ :=
  angleProductJacobian r x*onsiteCanceledDensity
    (fun i => globalRoot s (anglePoint r (x i))) (angleTuple r x)

theorem onsiteSourceIntegral_eq_angular (N : ℕ) (r : ℝ) (s : ℂ) :
    onsiteSourceIntegral N r s=(N.factorial:ℂ)⁻¹*∫ x in angleBox N,onsiteSourceAngularDensity r s x := by
  unfold onsiteSourceIntegral onsiteSourceAngularDensity
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Icc
  intro x _
  ring

theorem onsiteSourceAngularDensity_continuous (N : ℕ) {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    {s : ℂ} (hm : r⁻¹-r < (sourceS s).im) :
    Continuous (onsiteSourceAngularDensity (N := N) r s) := by
  have hs : s ≠ 0 := (dampingDomain_of_margin hr hr1 hm).1
  have hup (x : Fin N → ℝ) (i : Fin N) :
      0 < (sourceW s (angleTuple r x i)).im :=
    sourceW_upper_of_margin hr hr1 hm (anglePoint_norm hr.le _)
  have he (x : Fin N → ℝ) (i : Fin N) :
      selectedContinuedRoot s (angleTuple r x i) = globalRoot s (angleTuple r x i) :=
    continuedRoot_eq_interiorRoot (hup x i)
  have ha (x : Fin N → ℝ) : AnalyticAt ℂ (onsiteContinuedContourDensity N) (s,angleTuple r x) := by
    apply onsite_continuedContourDensity_analyticAt hs
    · intro i
      exact norm_ne_zero_iff.mp ((anglePoint_norm hr.le (x i)).trans_ne hr.ne')
    · intro i
      exact Or.inl (Or.inl (hup x i))
  have hc : Continuous (fun x : Fin N → ℝ => onsiteContinuedContourDensity N (s,angleTuple r x)) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (ha x).continuousAt.comp (f := fun x : Fin N → ℝ => (s,angleTuple r x))
      ((continuous_const.prodMk (angleTuple_continuous r)).continuousAt)
  have hpoint : onsiteSourceAngularDensity (N := N) r s =
      (fun x => ((2*(Real.pi:ℂ))⁻¹)^N*onsiteContinuedContourDensity N (s,angleTuple r x)) := by
    funext x
    unfold onsiteSourceAngularDensity onsiteContinuedContourDensity angleProductJacobian angleJacobian
    simp_rw [he]
    simp only [angleTuple,div_eq_mul_inv,Finset.prod_mul_distrib,Finset.prod_const,
      Finset.card_univ,Fintype.card_fin]
    ring
  rw [hpoint]
  exact continuous_const.mul hc

/-- The onsite physical integral is exactly its normalized iterated contour,
with no assumed Fubini or normalizing constant. -/
theorem onsiteSourceIntegral_eq_multiCircle (N : ℕ) {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    {s : ℂ} (hm : r⁻¹-r < (sourceS s).im) :
    onsiteSourceIntegral N r s = (N.factorial:ℂ)⁻¹ *
      multiCircleIntegral r N (fun y => onsiteCanceledDensity (fun i => globalRoot s (y i)) y) := by
  rw [onsiteSourceIntegral_eq_angular,multiCircleIntegral_eq_angle]
  change (N.factorial:ℂ)⁻¹ * (∫ x in angleBox N,onsiteSourceAngularDensity r s x) =
    (N.factorial:ℂ)⁻¹ * multiAngleIntegral N (onsiteSourceAngularDensity r s)
  rw [multiAngleIntegral_eq_box N _ (onsiteSourceAngularDensity_continuous N hr hr1 hm)]

theorem onsiteSourceIntegral_eq_formFactor (N : ℕ) {r : ℝ} (hr : 0<r) (hr1 : r<1)
    {s : ℂ} (hm : r⁻¹-r<(sourceS s).im) :
    onsiteSourceIntegral N r s=onsiteFormFactor N r s := by
  rw [onsiteSourceIntegral_eq_multiCircle N hr hr1 hm,
    onsite_residue_reduction N r hr s (globalRoot s)
      (fun y hy => (globalRoot_admissible hr hr1 hm).toTuple N y hy)]
  unfold reducedOnsiteFormFactor
  congr 1
  apply multiCircleIntegral_congr hr.le N
  intro y hy
  have hW (i : Fin N) : 0<(sourceW s (y i)).im := sourceW_upper_of_margin hr hr1 hm (hy i)
  have hroot : (fun i => selectedContinuedRoot s (y i))=(fun i => globalRoot s (y i)) :=
    funext (fun i => continuedRoot_eq_interiorRoot (hW i))
  rw [← hroot]
  apply onsite_canceledReducedDensity_continued_eq s y
  · intro i
    exact norm_ne_zero_iff.mp ((hy i).trans_ne hr.ne')
  · intro i
    exact Or.inl (Or.inl (hW i))
  · intro i j
    exact one_sub_mul_ne_zero_of_norm_lt_one ((hy i).trans_lt hr1) ((hy j).trans_lt hr1)

theorem onsiteSourceIntegral_eventually_formFactor (N : ℕ) {r : ℝ} (hr : 0<r) (hr1 : r<1)
    {s : ℂ} (hm : r⁻¹-r<(sourceS s).im) :
    onsiteSourceIntegral N r=ᶠ[𝓝 s] onsiteFormFactor N r := by
  filter_upwards [dampingDomain_mem_nhds (dampingDomain_of_margin hr hr1 hm)] with t ht
  exact onsiteSourceIntegral_eq_formFactor N hr hr1 ht.2

theorem upperOnsiteFormFactor_iteratedDeriv_eq_source (N : ℕ) (hN : 0<N)
    (j : ℕ) {r : ℝ} (hr : 0<r) (hr1 : r<1) {s : ℂ} (hm : r⁻¹-r<(sourceS s).im) :
    iteratedDeriv j (upperOnsiteFormFactor N) s=iteratedDeriv j (onsiteSourceIntegral N r) s := by
  rw [upperOnsiteFormFactor_iteratedDeriv_fixed_radius N hN j hr hr1 hm]
  exact ((onsiteSourceIntegral_eventually_formFactor N hr hr1 hm).iteratedDeriv_eq j).symm

end
end IsingBulk.HT.Contour
