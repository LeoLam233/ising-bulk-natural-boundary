import IsingBulk.First.FormFactorAnalytic
import IsingBulk.First.ReducedLocalization

/-! Fixed, temperature-independent localization weights preserve analyticity of
the actual normalized integrals. Residue equality transfers this regularity to
the selected root representation without differentiating a varying radius. -/
namespace IsingBulk.First
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators

theorem localizedDoubleFormFactor_analyticAt (N : ℕ) (hN : 0 < N) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) {s : ℂ} (hm : r⁻¹-r < (sourceS s).im)
    (w : ((Fin N → ℝ) × (Fin N → ℝ)) → ℝ) (hw : Continuous w) :
    AnalyticAt ℂ (fun t => localizedDoubleFormFactor N r t w) s := by
  have hs := dampingDomain_of_margin hr hr1 hm
  have hroot := globalRoot_admissible hr hr1 hm
  have htuple : ∀ θ : Fin N → ℝ, ResidueAdmissible r s (angleTuple r θ)
      (fun i => globalRoot s (anglePoint r (θ i))) := by
    intro θ
    exact hroot.toTuple N _ (fun _ => anglePoint_norm hr.le _)
  let A : (Fin N → ℂ) → (Fin N → ℂ) → ℂ := fun x y =>
    ((coordinateProduct x)⁻¹+(coordinateProduct y)⁻¹)/
      ((1-coordinateProduct x)*(1-coordinateProduct y))*pairProduct x*pairProduct y
  have hfac (t : ℂ) (x y : Fin N → ℂ) :
      doubleDensity t x y = A x y*∏ i, (dispersion (x i) (y i) t)⁻¹ := by
    dsimp only [A, doubleDensity, commonDensity]
    ring
  have hD := doubleDensity_continuous_angles N hN r s (globalRoot s) htuple
  have hA : Continuous (fun p : (Fin N → ℝ) × (Fin N → ℝ) => A (angleTuple r p.1) (angleTuple r p.2)) := by
    apply spatialAmplitude_continuous hr hr1 hs A
    simpa only [angularResolventProduct_eq, ← hfac] using hD
  let aw : ((Fin N → ℝ) × (Fin N → ℝ)) → ℂ := fun p =>
    (w p:ℂ)*angleProductJacobian r p.2*angleProductJacobian r p.1*A (angleTuple r p.1) (angleTuple r p.2)
  have hJ := angleProductJacobian_continuous (N := N) r
  have haw : Continuous aw :=
    ((((Complex.continuous_ofReal.comp hw).mul (hJ.comp continuous_snd)).mul
      (hJ.comp continuous_fst))).mul hA
  have ha := (analyticAt_const (𝕜 := ℂ) (x := s) (v := (N.factorial:ℂ)⁻¹)).mul
    (angularResolventIntegral_analyticAt N hr hr1 aw haw hs)
  convert! ha using 1
  funext t
  dsimp only [Pi.mul_apply, localizedDoubleFormFactor]
  congr 1
  apply setIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Icc)
  intro p _
  dsimp only [localizedDoubleAngleDensity, aw]
  rw [hfac, angularResolventProduct_eq]
  ring

theorem weightedDoubleFormFactor_analyticAt (N : ℕ) (hN : 0 < N) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) {s : ℂ} (hm : r⁻¹-r < (sourceS s).im)
    (w : (Fin N → ℝ) → ℝ) (hw : Continuous w) :
    AnalyticAt ℂ (fun t => weightedDoubleFormFactor N r t w) s := by
  apply (localizedDoubleFormFactor_analyticAt N hN hr hr1 hm
    (fun p => w p.2) (hw.comp continuous_snd)).congr
  filter_upwards [dampingDomain_mem_nhds (dampingDomain_of_margin hr hr1 hm)] with t ht
  symm
  apply weightedDoubleFormFactor_eq_product_integral N hN r t (globalRoot t) _ w hw
  intro θ
  exact (globalRoot_admissible hr hr1 ht.2).toTuple N _ (fun _ => anglePoint_norm hr.le _)

theorem weightedReducedFormFactor_analyticAt (N : ℕ) (hN : 0 < N) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) {s : ℂ} (hm : r⁻¹-r < (sourceS s).im)
    (w : (Fin N → ℝ) → ℝ) (hw : Continuous w) :
    AnalyticAt ℂ (fun t => weightedReducedFormFactor N r (globalRoot t) w) s := by
  apply (weightedDoubleFormFactor_analyticAt N hN hr hr1 hm w hw).congr
  filter_upwards [dampingDomain_mem_nhds (dampingDomain_of_margin hr hr1 hm)] with t ht
  apply weighted_residue_reduction N hN r t (globalRoot t) w
  intro θ
  exact (globalRoot_admissible hr hr1 ht.2).toTuple N _ (fun _ => anglePoint_norm hr.le _)

/-- Differentiation distributes over the two literal selected residues and the
literal untouched complement, for every order. -/
theorem upperFormFactor_iteratedDeriv_split (N : ℕ) (hN : 0 < N) (j : ℕ) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) {s : ℂ} (hm : r⁻¹-r < (sourceS s).im)
    (u v : (Fin N → ℝ) → ℝ) (hu : Continuous u) (hv : Continuous v) :
    iteratedDeriv j (upperFormFactor N) s =
      iteratedDeriv j (fun t => weightedReducedFormFactor N r (globalRoot t) u) s +
      iteratedDeriv j (fun t => weightedReducedFormFactor N r (globalRoot t) v) s +
      iteratedDeriv j (fun t => localizedDoubleFormFactor N r t (fun p => 1-u p.2-v p.2)) s := by
  have hU := weightedReducedFormFactor_analyticAt N hN hr hr1 hm u hu
  have hV := weightedReducedFormFactor_analyticAt N hN hr hr1 hm v hv
  have hC := localizedDoubleFormFactor_analyticAt N hN hr hr1 hm
    (fun p => 1-u p.2-v p.2)
    ((continuous_const.sub (hu.comp continuous_snd)).sub (hv.comp continuous_snd))
  rw [upperFormFactor_iteratedDeriv_reduced_localization N hN j hr hr1 hm u v hu hv]
  unfold reducedLocalizedSum
  have hUV : AnalyticAt ℂ (fun t => weightedReducedFormFactor N r (globalRoot t) u +
      weightedReducedFormFactor N r (globalRoot t) v) s := by
    convert! hU.add hV using 1
  rw [iteratedDeriv_fun_add hUV.contDiffAt hC.contDiffAt,
    iteratedDeriv_fun_add hU.contDiffAt hV.contDiffAt]

end
end IsingBulk.First
