import IsingBulk.First.DoublePeriodicBump
import IsingBulk.First.SourceAngularPeriodicity
import IsingBulk.First.ComplementLocalBound
import Mathlib.MeasureTheory.Group.Prod

/-! The literal product-torus localized integral equals its compact full-space
lift even when the chart center lies on a fundamental-domain seam. -/
namespace IsingBulk.First
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff Topology

theorem doublePeriodicizeBump_integral (N : ℕ) (c : DoubleAngularVector N)
    (w : DoubleAngularVector N → ℝ) (hw : ContDiff ℝ ∞ w)
    (hsmall : ∀ u, w u ≠ 0 → ∀ i, |u.1 i-c.1 i| ≤ 1/2 ∧ |u.2 i-c.2 i| ≤ 1/2)
    (F : DoubleAngularVector N → ℂ) (hF : Continuous F)
    (hper : DoubleCoordinatePeriodicSections N F) :
    (∫ u in angleBox N ×ˢ angleBox N, (doublePeriodicizeBump c w u:ℂ)*F u) =
      ∫ u, (w u:ℂ)*F u := by
  let f : DoubleAngularVector N → ℂ := fun u => (doublePeriodicizeBump c w u:ℂ)*F u
  let d : DoubleAngularVector N := ((fun i => c.1 i-Real.pi),(fun i => c.2 i-Real.pi))
  have hfc : Continuous f :=
    (Complex.continuous_ofReal.comp (doublePeriodicizeBump_contDiff c w hw hsmall).continuous).mul hF
  have hfp : DoubleCoordinatePeriodicSections N f := by
    constructor
    · intro y x i
      dsimp only [f]
      rw [(doublePeriodicizeBump_periodic c w (x,y) i).1]
      exact congrArg (fun z => (doublePeriodicizeBump c w (x,y):ℂ)*z) (hper.1 y x i)
    · intro x y i
      dsimp only [f]
      rw [(doublePeriodicizeBump_periodic c w (x,y) i).2]
      exact congrArg (fun z => (doublePeriodicizeBump c w (x,y):ℂ)*z) (hper.2 x y i)
  calc
    _ = ∫ u in angleBox N ×ˢ angleBox N, f (u+d) :=
      (doubleAngleBox_integral_shift N f hfc hfp d).symm
    _ = ∫ u in angleBox N ×ˢ angleBox N, (w (u+d):ℂ)*F (u+d) := by
      apply setIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Icc)
      intro u hu
      dsimp only [f]
      rw [doublePeriodicizeBump_eq_on_centeredBox c w hsmall]
      · intro i
        have h1 := hu.1.1 i
        have h2 := hu.1.2 i
        dsimp only [d,Prod.fst_add,Pi.add_apply]
        constructor <;> linarith
      · intro i
        have h1 := hu.2.1 i
        have h2 := hu.2.2 i
        dsimp only [d,Prod.snd_add,Pi.add_apply]
        constructor <;> linarith
    _ = ∫ u : DoubleAngularVector N, (w (u+d):ℂ)*F (u+d) := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro u hu
      have hz : w (u+d)=0 := by
        by_contra hn
        apply hu
        constructor
        · constructor <;> intro i
          · have hh := abs_le.mp (hsmall (u+d) hn i).1
            dsimp only [d,Prod.fst_add,Pi.add_apply] at hh
            linarith [hh.1,Real.pi_gt_three]
          · have hh := abs_le.mp (hsmall (u+d) hn i).1
            dsimp only [d,Prod.fst_add,Pi.add_apply] at hh
            linarith [hh.2,Real.pi_gt_three]
        · constructor <;> intro i
          · have hh := abs_le.mp (hsmall (u+d) hn i).2
            dsimp only [d,Prod.snd_add,Pi.add_apply] at hh
            linarith [hh.1,Real.pi_gt_three]
          · have hh := abs_le.mp (hsmall (u+d) hn i).2
            dsimp only [d,Prod.snd_add,Pi.add_apply] at hh
            linarith [hh.2,Real.pi_gt_three]
      rw [hz,Complex.ofReal_zero,zero_mul]
    _ = _ := by
      rw [Measure.volume_eq_prod]
      exact integral_add_right_eq_self (fun u => (w u:ℂ)*F u) d

/-- The actual Ising density, the original angular box and N! are retained.
This is the exact bridge from compact lifted chart estimates to torus pieces. -/
theorem localizedDoubleFormFactor_periodicLift (N : ℕ) (hN : 0 < N) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) {s : ℂ} (hm : r⁻¹-r < (sourceS s).im)
    (c : DoubleAngularVector N) (w : DoubleAngularVector N → ℝ) (hw : ContDiff ℝ ∞ w)
    (hsmall : ∀ u, w u ≠ 0 → ∀ i, |u.1 i-c.1 i| ≤ 1/2 ∧ |u.2 i-c.2 i| ≤ 1/2) :
    localizedDoubleFormFactor N r s (doublePeriodicizeBump c w) =
      liftedLocalizedDoubleFormFactor N r s w := by
  have hroot := globalRoot_admissible hr hr1 hm
  have hd := doubleDensity_continuous_angles N hN r s (globalRoot s)
    (fun θ => hroot.toTuple N _ (fun _ => anglePoint_norm hr.le _))
  have he := doublePeriodicizeBump_integral N c w hw hsmall
    (doubleAngularDensityOf r (doubleDensity s))
    (doubleAngularDensityOf_continuous N r _ hd) (doubleAngularDensityOf_periodic N r s)
  unfold localizedDoubleFormFactor liftedLocalizedDoubleFormFactor
  congr 1
  simpa only [localizedDoubleAngleDensity,doubleAngularDensityOf,mul_assoc] using he

theorem localizedDoubleFormFactor_iteratedDeriv_periodicLift (N : ℕ) (hN : 0 < N) (j : ℕ)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) {s : ℂ} (hm : r⁻¹-r < (sourceS s).im)
    (c : DoubleAngularVector N) (w : DoubleAngularVector N → ℝ) (hw : ContDiff ℝ ∞ w)
    (hsmall : ∀ u, w u ≠ 0 → ∀ i, |u.1 i-c.1 i| ≤ 1/2 ∧ |u.2 i-c.2 i| ≤ 1/2) :
    iteratedDeriv j (fun t => localizedDoubleFormFactor N r t (doublePeriodicizeBump c w)) s =
      iteratedDeriv j (fun t => liftedLocalizedDoubleFormFactor N r t w) s := by
  apply Filter.EventuallyEq.iteratedDeriv_eq j
  filter_upwards [dampingDomain_mem_nhds (dampingDomain_of_margin hr hr1 hm)] with t ht
  exact localizedDoubleFormFactor_periodicLift N hN hr hr1 ht.2 c w hw hsmall

end
end IsingBulk.First
