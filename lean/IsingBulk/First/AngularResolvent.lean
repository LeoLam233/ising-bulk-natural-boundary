import IsingBulk.First.ResolventParameterIntegral
import IsingBulk.First.NormalizationIntegral
import IsingBulk.First.MixedRadiusDamping

/-! The actual angular source resolvents, with a fixed admissible radius and an
open complex temperature neighborhood. -/
namespace IsingBulk.First
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators

def dampingDomain (r : ℝ) : Set ℂ := {s | s ≠ 0 ∧ r⁻¹-r < (sourceS s).im}

theorem dampingDomain_mem_nhds {r : ℝ} {s : ℂ} (hs : s ∈ dampingDomain r) :
    dampingDomain r ∈ 𝓝 s := by
  have hS : ContinuousAt (fun t : ℂ => (sourceS t).im) s :=
    Complex.continuous_im.continuousAt.comp_of_eq
      (continuousAt_id.add (continuousAt_id.inv₀ hs.1)) rfl
  exact Filter.inter_mem (isOpen_compl_singleton.mem_nhds hs.1)
    (hS.eventually (Ioi_mem_nhds hs.2))

def angularDispersionTrace {N : ℕ} (r : ℝ) (i : Fin N)
    (p : (Fin N → ℝ) × (Fin N → ℝ)) : ℂ :=
  (anglePoint r (p.1 i)+(anglePoint r (p.1 i))⁻¹)/2 +
    (anglePoint r (p.2 i)+(anglePoint r (p.2 i))⁻¹)/2

theorem angularDispersionTrace_continuous {N : ℕ} {r : ℝ} (hr : 0 < r) (i : Fin N) :
    Continuous (angularDispersionTrace r i) := by
  have hx : Continuous (fun p : (Fin N → ℝ) × (Fin N → ℝ) => anglePoint r (p.1 i)) :=
    (continuous_circleMap 0 r).comp ((continuous_apply i).comp continuous_fst)
  have hy : Continuous (fun p : (Fin N → ℝ) × (Fin N → ℝ) => anglePoint r (p.2 i)) :=
    (continuous_circleMap 0 r).comp ((continuous_apply i).comp continuous_snd)
  have hn (a : ℝ) : anglePoint r a ≠ 0 :=
    norm_pos_iff.mp ((anglePoint_norm hr.le a).symm ▸ hr)
  exact ((hx.add (hx.inv₀ (fun p => hn (p.1 i)))).div_const 2).add
    ((hy.add (hy.inv₀ (fun p => hn (p.2 i)))).div_const 2)

theorem sourceS_sub_angularDispersionTrace {N : ℕ} (r : ℝ) (s : ℂ) (i : Fin N)
    (p : (Fin N → ℝ) × (Fin N → ℝ)) :
    sourceS s-angularDispersionTrace r i p =
      dispersion (angleTuple r p.1 i) (angleTuple r p.2 i) s := by
  unfold angularDispersionTrace dispersion angleTuple
  ring

theorem angularDispersion_ne_zero {N : ℕ} {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    {s : ℂ} (hs : s ∈ dampingDomain r) (p : (Fin N → ℝ) × (Fin N → ℝ)) (i : Fin N) :
    sourceS s-angularDispersionTrace r i p ≠ 0 := by
  rw [sourceS_sub_angularDispersionTrace]
  have hx : ‖angleTuple r p.1 i‖=r := anglePoint_norm hr.le _
  have hy : ‖angleTuple r p.2 i‖=r := anglePoint_norm hr.le _
  have him := dispersion_im_positive_on_annulus hr (le_of_eq hx.symm) (le_of_eq hy.symm)
    (hx.trans_le hr1.le) (hy.trans_le hr1.le) hs.2
  exact fun he => (ne_of_gt him) (congrArg Complex.im he)

theorem angularResolventProduct_eq {N : ℕ} (r : ℝ) (s : ℂ)
    (p : (Fin N → ℝ) × (Fin N → ℝ)) :
    sourceResolventProduct (angularDispersionTrace r) s p =
      ∏ i, (dispersion (angleTuple r p.1 i) (angleTuple r p.2 i) s)⁻¹ := by
  unfold sourceResolventProduct
  simp_rw [sourceS_sub_angularDispersionTrace]

theorem angularResolventProduct_continuous {N : ℕ} {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    {s : ℂ} (hs : s ∈ dampingDomain r) :
    Continuous (sourceResolventProduct (angularDispersionTrace (N := N) r) s) := by
  apply continuous_finsetProd
  intro i _
  exact (continuous_const.sub (angularDispersionTrace_continuous hr i)).inv₀
    (fun p => angularDispersion_ne_zero hr hr1 hs p i)

/-- Every fixed continuous angular amplitude, including localized weights,
retains genuine holomorphic dependence on the source temperature. -/
theorem angularResolventIntegral_analyticAt (N : ℕ) {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (w : ((Fin N → ℝ) × (Fin N → ℝ)) → ℂ) (hw : Continuous w)
    {s : ℂ} (hs : s ∈ dampingDomain r) :
    AnalyticAt ℂ (fun t => ∫ p in angleBox N ×ˢ angleBox N,
      w p*sourceResolventProduct (angularDispersionTrace r) t p) s := by
  apply DifferentiableOn.analyticAt (s := dampingDomain r) _ (dampingDomain_mem_nhds hs)
  intro t ht
  exact (resolventIntegral_differentiableAt (isCompact_Icc.prod isCompact_Icc)
    (angularDispersionTrace r) (angularDispersionTrace_continuous hr) w hw
    (dampingDomain_mem_nhds ht) (fun _ h => h.1)
    (fun _ h p i => angularDispersion_ne_zero hr hr1 h p i)).differentiableWithinAt

end
end IsingBulk.First
