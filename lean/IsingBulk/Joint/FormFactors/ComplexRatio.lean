import IsingBulk.Joint.Geometry.TransferChart
import IsingBulk.Joint.Transverse.CurveCoordinates
import IsingBulk.Joint.Negative.CurveCoordinates

/-! Actual complex-ratio coordinates and a parameter-dependent analytic
implicit function on a common product polydisk, JOINT Lemma 7.1. -/
namespace IsingBulk.Joint.FormFactors
noncomputable section
open Set Filter Metric ContinuousLinearMap
open scoped Topology

/-- Both entries are complex and independent. -/
def complexRatioMap (q : Coupling) : Coupling := (q.1,q.2*q.1)

def complexRatioDerivative (q : Coupling) : Coupling →L[ℂ] Coupling :=
  (fst ℂ ℂ ℂ).prod (q.2 • fst ℂ ℂ ℂ+q.1 • snd ℂ ℂ ℂ)

theorem complexRatioMap_analyticAt (q : Coupling) : AnalyticAt ℂ complexRatioMap q :=
  analyticAt_fst.prod (analyticAt_snd.mul analyticAt_fst)

theorem complexRatioMap_hasStrictFDerivAt (q : Coupling) :
    HasStrictFDerivAt complexRatioMap (complexRatioDerivative q) q := by
  have hz : HasStrictFDerivAt (fun v : Coupling => v.1) (fst ℂ ℂ ℂ) q := hasStrictFDerivAt_fst
  have hw : HasStrictFDerivAt (fun v : Coupling => v.2) (snd ℂ ℂ ℂ) q := hasStrictFDerivAt_snd
  convert! hz.prodMk (hw.fun_mul hz) using 1

/-- The determinant is computed from the actual Fréchet derivative. -/
theorem complexRatioMap_jacobian (q : Coupling) :
    (fderiv ℂ complexRatioMap q (1,0)).1*(fderiv ℂ complexRatioMap q (0,1)).2-
      (fderiv ℂ complexRatioMap q (0,1)).1*(fderiv ℂ complexRatioMap q (1,0)).2=q.1 := by
  rw [(complexRatioMap_hasStrictFDerivAt q).hasFDerivAt.fderiv]
  simp [complexRatioDerivative]

private theorem twoByTwo_bijective (f : Coupling →L[ℂ] Coupling)
    (hd : (f (1,0)).1*(f (0,1)).2-(f (0,1)).1*(f (1,0)).2≠0) : Function.Bijective f := by
  let a := (f (1,0)).1
  let b := (f (0,1)).1
  let c := (f (1,0)).2
  let d := (f (0,1)).2
  change a*d-b*c≠0 at hd
  have he (v : Coupling) : f v=(a*v.1+b*v.2,c*v.1+d*v.2) := by
    have hv : v=v.1 • (1,0)+v.2 • (0,1) := by ext <;> simp
    calc
      f v = f (v.1 • (1,0)+v.2 • (0,1)) := congrArg f hv
      _ = _ := by
        rw [map_add,map_smul,map_smul]
        ext <;> simp [a,b,c,d,smul_eq_mul,mul_comm]
  constructor
  · intro v w hv
    have h1 := congrArg Prod.fst hv
    have h2 := congrArg Prod.snd hv
    rw [he,he] at h1 h2
    have he1 : (a*d-b*c)*(v.1-w.1)=0 := by linear_combination d*h1-b*h2
    have he2 : (a*d-b*c)*(v.2-w.2)=0 := by linear_combination a*h2-c*h1
    exact Prod.ext (sub_eq_zero.mp ((mul_eq_zero.mp he1).resolve_left hd))
      (sub_eq_zero.mp ((mul_eq_zero.mp he2).resolve_left hd))
  · intro v
    refine ⟨((d*v.1-b*v.2)/(a*d-b*c),(a*v.2-c*v.1)/(a*d-b*c)),?_⟩
    rw [he]
    apply Prod.ext <;> dsimp
    · rw [← mul_div_assoc,← mul_div_assoc,← add_div,div_eq_iff hd]
      ring
    · rw [← mul_div_assoc,← mul_div_assoc,← add_div,div_eq_iff hd]
      ring

/-- Genuine multivariable analytic inverse from the actual derivative. -/
theorem exists_joint_analytic_local_inverse {f : Coupling → Coupling} {q : Coupling}
    (hf : AnalyticAt ℂ f q) (hb : Function.Bijective (fderiv ℂ f q)) :
    ∃ e : OpenPartialHomeomorph Coupling Coupling,
      q∈e.source ∧ (e : Coupling → Coupling)=f ∧ AnalyticAt ℂ e.symm (f q) := by
  let d : Coupling ≃L[ℂ] Coupling := ContinuousLinearEquiv.ofBijective
    (fderiv ℂ f q) (LinearMap.ker_eq_bot.mpr hb.1) (LinearMap.range_eq_top.mpr hb.2)
  have hd : HasStrictFDerivAt f (d : Coupling →L[ℂ] Coupling) q := hf.hasStrictFDerivAt
  let e := hd.toOpenPartialHomeomorph f
  have he : (e : Coupling → Coupling)=f := hd.toOpenPartialHomeomorph_coe
  have hq : q∈e.source := hd.mem_toOpenPartialHomeomorph_source
  have ha : AnalyticAt ℂ e q := by rwa [he]
  refine ⟨e,hq,he,?_⟩
  rcases ha with ⟨ps,hps⟩
  have hp1 : ps 1=(continuousMultilinearCurryFin1 ℂ Coupling Coupling).symm
      (d : Coupling →L[ℂ] Coupling) := by
    apply (continuousMultilinearCurryFin1 ℂ Coupling Coupling).injective
    rw [LinearIsometryEquiv.apply_symm_apply]
    have hd' : HasFDerivAt (e : Coupling → Coupling) (d : Coupling →L[ℂ] Coupling) q := by
      rw [he]; exact hd.hasFDerivAt
    exact hps.hasFDerivAt.unique hd'
  simpa only [he] using (e.hasFPowerSeriesAt_symm hq hps hp1).analyticAt

theorem complexRatioMap_local_biholomorphism {q : Coupling} (hz : q.1≠0) :
    ∃ e : OpenPartialHomeomorph Coupling Coupling,
      q∈e.source ∧ (e : Coupling → Coupling)=complexRatioMap ∧
      AnalyticAt ℂ e.symm (complexRatioMap q) := by
  apply exists_joint_analytic_local_inverse (complexRatioMap_analyticAt q)
  apply twoByTwo_bijective
  rwa [complexRatioMap_jacobian]

/-- The augmented edge map retains lambda as its second coordinate. -/
def ratioEdgeMap (edge : Coupling → ℂ) (q : Coupling) : Coupling :=
  (edge (complexRatioMap q),q.2)

theorem ratioEdgeMap_local_biholomorphism {edge : Coupling → ℂ} {q : Coupling}
    (he : AnalyticAt ℂ edge (complexRatioMap q))
    (hd : deriv (fun z => edge (z,q.2*z)) q.1≠0) :
    ∃ e : OpenPartialHomeomorph Coupling Coupling,
      q∈e.source ∧ (e : Coupling → Coupling)=ratioEdgeMap edge ∧
      AnalyticAt ℂ e.symm (ratioEdgeMap edge q) := by
  let f : Coupling → ℂ := edge ∘ complexRatioMap
  have hf : AnalyticAt ℂ f q := he.comp (complexRatioMap_analyticAt q)
  have hder := hf.hasStrictFDerivAt.hasFDerivAt.prodMk (hasFDerivAt_snd (𝕜 := ℂ) (p := q))
  have hslice : deriv (fun z => edge (z,q.2*z)) q.1=fderiv ℂ f q (1,0) := by
    have hh := hf.hasStrictFDerivAt.hasFDerivAt.comp_hasDerivAt q.1
      ((hasDerivAt_id q.1).prodMk (hasDerivAt_const q.1 q.2))
    exact hh.deriv
  apply exists_joint_analytic_local_inverse (hf.prod analyticAt_snd)
  apply twoByTwo_bijective
  change (fderiv ℂ (fun v => (f v,v.2)) q (1,0)).1*
    (fderiv ℂ (fun v => (f v,v.2)) q (0,1)).2-
    (fderiv ℂ (fun v => (f v,v.2)) q (0,1)).1*
    (fderiv ℂ (fun v => (f v,v.2)) q (1,0)).2≠0
  rw [hder.fderiv]
  simpa using hslice ▸ hd

/-- Actual complex lambda is retained while the edge parameter is inverted.
The same closed product polydisk lies inside an analytic neighborhood and any
prescribed open strict-face neighborhood. Both inverse identities are retained. -/
theorem exists_complex_ratio_edge_polydisk {edge : Coupling → ℂ} {z₀ lam₀ : ℂ}
    (he : AnalyticAt ℂ edge (z₀,lam₀*z₀)) (he0 : edge (z₀,lam₀*z₀)=0)
    (hd : deriv (fun z => edge (z,lam₀*z)) z₀≠0)
    {V : Set Coupling} (hV : IsOpen V) (hKV : (z₀,lam₀*z₀)∈V) :
    ∃ Z : Coupling → ℂ, ∃ family : Coupling → Coupling, ∃ r : ℝ,
      0<r ∧ family=(fun q => complexRatioMap (Z q,q.2)) ∧
      Z (0,lam₀)=z₀ ∧ family (0,lam₀)=(z₀,lam₀*z₀) ∧
      (∀ u lam : ℂ, ‖u‖≤2*r → ‖lam-lam₀‖≤2*r →
        AnalyticAt ℂ Z (u,lam) ∧ AnalyticAt ℂ family (u,lam) ∧
        edge (family (u,lam))=u ∧ family (u,lam)∈V) ∧
      (∀ᶠ q : Coupling in 𝓝 (z₀,lam₀), Z (edge (complexRatioMap q),q.2)=q.1) := by
  obtain ⟨e,hq,heq,hpsi⟩ := ratioEdgeMap_local_biholomorphism (q := (z₀,lam₀)) he hd
  have hq0 : ratioEdgeMap edge (z₀,lam₀)=(0,lam₀) := Prod.ext he0 rfl
  have hpa : AnalyticAt ℂ e.symm (0,lam₀) := by rwa [hq0] at hpsi
  have hp0 : e.symm (0,lam₀)=(z₀,lam₀) := by
    have hh := e.left_inv hq
    rwa [heq,hq0] at hh
  let Z : Coupling → ℂ := fun q => (e.symm q).1
  let family : Coupling → Coupling := fun q => complexRatioMap (Z q,q.2)
  have hZa : AnalyticAt ℂ Z (0,lam₀) := analyticAt_fst.comp hpa
  have hFa : AnalyticAt ℂ family (0,lam₀) :=
    (complexRatioMap_analyticAt _).comp (hZa.prod analyticAt_snd)
  have hZ0 : Z (0,lam₀)=z₀ := congrArg Prod.fst hp0
  have hF0 : family (0,lam₀)=(z₀,lam₀*z₀) := by simp [family,complexRatioMap,hZ0]
  have hright : ∀ᶠ q in 𝓝 (0,lam₀), edge (family q)=q.1 := by
    have ht := e.open_target.mem_nhds (e.map_source hq)
    rw [heq,hq0] at ht
    filter_upwards [ht] with q hqt
    have hh := e.right_inv hqt
    rw [heq] at hh
    have hs := congrArg Prod.snd hh
    change (e.symm q).2=q.2 at hs
    have hf := congrArg Prod.fst hh
    change edge (complexRatioMap (Z q,q.2))=q.1
    simpa only [ratioEdgeMap,Prod.fst,←hs,Z,Prod.mk.eta] using hf
  have hFV : ∀ᶠ q in 𝓝 (0,lam₀), family q∈V :=
    hFa.continuousAt.eventually (hV.mem_nhds (hF0 ▸ hKV))
  have hall := hZa.eventually_analyticAt.and (hFa.eventually_analyticAt.and (hright.and hFV))
  obtain ⟨R,hR,hallR⟩ := Metric.mem_nhds_iff.mp hall
  refine ⟨Z,family,R/3,by positivity,rfl,hZ0,hF0,?_,?_⟩
  · intro u lam hu hl
    apply hallR
    have hh : max ‖u‖ ‖lam-lam₀‖<R := max_lt_iff.mpr ⟨by linarith,by linarith⟩
    simpa only [mem_ball,Prod.dist_eq,dist_eq_norm,Prod.norm_def,
      Prod.fst_sub,Prod.snd_sub,sub_zero] using hh
  · filter_upwards [e.open_source.mem_nhds hq] with q hqs
    have hh := e.left_inv hqs
    rw [heq] at hh
    exact congrArg Prod.fst hh

end
end IsingBulk.Joint.FormFactors
