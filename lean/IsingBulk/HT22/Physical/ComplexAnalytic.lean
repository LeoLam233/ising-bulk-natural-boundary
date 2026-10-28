import IsingBulk.HT22.Physical.Holomorphy
namespace IsingBulk.HT22.Physical
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.HT.Contour Set Filter MeasureTheory
open scoped Topology BigOperators
theorem complexSignedDensity_analyticAt_of_off_segment (negative : Bool) {N : ℕ}
    (hN : 0 < N) {t : ℂ} (ht0 : t≠0) (phi : Fin N → ℂ)
    (hW : ∀ i,IsingBulk.Preferred22.OffRealSegment (t+t⁻¹-Complex.cos (phi i))) :
    AnalyticAt ℂ (@complexSignedDensity negative N) (t, phi) := by
  let p : ℂ × (Fin N → ℂ) := (t, phi)
  have dq (i : Fin N) : AnalyticAt ℂ (fun x : ℂ × (Fin N → ℂ) => x.2 i) p :=
    (ContinuousLinearMap.proj i : (Fin N → ℂ) →L[ℂ] ℂ).analyticAt _ |>.comp analyticAt_snd
  have dy (i : Fin N) : AnalyticAt ℂ (fun x : ℂ × (Fin N → ℂ) => complexAngle (x.2 i)) p :=
    (analyticAt_const.mul (dq i)).cexp
  have dS : AnalyticAt ℂ (fun x : ℂ × (Fin N → ℂ) => x.1+x.1⁻¹) p :=
    analyticAt_fst.add (analyticAt_fst.inv ht0)
  have dz (i : Fin N) : AnalyticAt ℂ (fun x : ℂ × (Fin N → ℂ) => complexRoot x.1 (x.2 i)) p := by
    have dW := dS.sub (Complex.analyticAt_cos.comp (dq i))
    exact (IsingBulk.Preferred22.physicalRoot_analyticAt (hW i)).comp_of_eq dW rfl
  have hn (i : Fin N) : ‖complexRoot p.1 (p.2 i)‖ < 1 :=
    IsingBulk.Preferred22.physicalRoot_inside (hW i)
  have hpair (i j : Fin N) : 1-complexRoot p.1 (p.2 i)*complexRoot p.1 (p.2 j) ≠ 0 :=
    one_sub_mul_ne_zero_of_norm_lt_one (hn i) (hn j)
  have hZ : 1-constraintSign negative*∏ i, complexRoot p.1 (p.2 i) ≠ 0 :=
    signed_product_gap_ne_zero hN _ (constraintSign_norm negative) _ hn
  have dZ := Finset.univ.analyticAt_fun_prod (fun i _ => dz i)
  have dbody : AnalyticAt ℂ (fun x : ℂ × (Fin N → ℂ) =>
      ∏ i, oneBody (complexRoot x.1 (x.2 i))) p := by
    simp_rw [oneBody_eq_rational]
    apply Finset.univ.analyticAt_fun_prod
    intro i _
    exact (analyticAt_const.mul (dz i)).div (analyticAt_const.sub ((dz i).pow 2))
      (by simpa only [pow_two] using hpair i i)
  have dpair (i j : Fin N) : AnalyticAt ℂ (fun x : ℂ × (Fin N → ℂ) =>
      canceledPair (complexAngle (x.2 i)) (complexAngle (x.2 j))
        (complexRoot x.1 (x.2 i)) (complexRoot x.1 (x.2 j))) p := by
    exact (((((dy i).sub (dy j)).pow 2).neg.mul (dz i)).mul (dz j)).div
      (((dy i).mul (dy j)).mul ((analyticAt_const.sub ((dz i).mul (dz j))).pow 2))
      (mul_ne_zero (mul_ne_zero (Complex.exp_ne_zero _) (Complex.exp_ne_zero _))
        (pow_ne_zero 2 (hpair i j)))
  have dpairs : AnalyticAt ℂ (fun x : ℂ × (Fin N → ℂ) =>
      canceledPairProduct (fun i => complexRoot x.1 (x.2 i))
        (fun i => complexAngle (x.2 i))) p := by
    apply Finset.univ.analyticAt_fun_prod
    intro i _
    apply (Finset.univ.filter (fun j => i < j)).analyticAt_fun_prod
    intro j _
    exact dpair i j
  exact (((analyticAt_const.add (analyticAt_const.mul dZ)).div
    (analyticAt_const.sub (analyticAt_const.mul dZ)) hZ).mul dbody).mul dpairs

end
end IsingBulk.HT22.Physical
