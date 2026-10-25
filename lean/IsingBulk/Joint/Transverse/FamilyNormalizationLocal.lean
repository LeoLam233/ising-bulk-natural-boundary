import IsingBulk.Joint.FormFactors.ComplexRatio

/-! Parameter-preserving analytic inverse maps for arbitrary complex families.
The parameter space is not restricted to the ratio coordinate. -/
namespace IsingBulk.Joint.Transverse
noncomputable section
open Set Filter Metric ContinuousLinearMap
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

def familyEdgeMap (f : ℂ × E → ℂ) (q : ℂ × E) : ℂ × E := (f q,q.2)

omit [CompleteSpace E] in
theorem family_linear_triangular_bijective (D : (ℂ × E) →L[ℂ] ℂ)
    (ha : D (1,0)≠0) : Function.Bijective (D.prod (snd ℂ ℂ E)) := by
  have he (z : ℂ) (eta : E) : D (z,eta)=z*D (1,0)+D (0,eta) := by
    have hv : (z,eta)=z • ((1,0):ℂ × E)+(0,eta) := by ext <;> simp
    rw [hv,map_add,map_smul]
    rfl
  constructor
  · intro x y h
    rcases x with ⟨x,eta⟩
    rcases y with ⟨y,theta⟩
    change (D (x,eta),eta)=(D (y,theta),theta) at h
    have h2 : eta=theta := congrArg Prod.snd h
    have h1 : D (x,eta)=D (y,theta) := congrArg Prod.fst h
    rw [he x eta,he y theta,h2] at h1
    exact Prod.ext (mul_right_cancel₀ ha (add_right_cancel h1)) h2
  · intro y
    refine ⟨((y.1-D (0,y.2))/D (1,0),y.2),?_⟩
    apply Prod.ext
    · change D ((y.1-D (0,y.2))/D (1,0),y.2)=y.1
      rw [he,div_mul_cancel₀ _ ha]
      ring
    · rfl

omit [CompleteSpace E] in
theorem family_slice_deriv_eq {f : ℂ × E→ℂ} {q : ℂ × E}
    (hf : AnalyticAt ℂ f q) :
    deriv (fun z=>f (z,q.2)) q.1=fderiv ℂ f q (1,0) := by
  exact (hf.hasStrictFDerivAt.hasFDerivAt.comp_hasDerivAt q.1
    ((hasDerivAt_id q.1).prodMk (hasDerivAt_const q.1 q.2))).deriv

/-- Actual joint IFT on `(z,eta) ↦ (f(z,eta),eta)`. -/
theorem familyEdgeMap_local_inverse {f : ℂ × E→ℂ} {q : ℂ × E}
    (hf : AnalyticAt ℂ f q) (hd : deriv (fun z=>f (z,q.2)) q.1≠0) :
    ∃ e : OpenPartialHomeomorph (ℂ × E) (ℂ × E),
      q∈e.source ∧ (e : (ℂ × E)→(ℂ × E))=familyEdgeMap f ∧
      AnalyticAt ℂ e.symm (familyEdgeMap f q) := by
  have hF : AnalyticAt ℂ (familyEdgeMap f) q := hf.prod analyticAt_snd
  have hder : HasFDerivAt (familyEdgeMap f)
      ((fderiv ℂ f q).prod (snd ℂ ℂ E)) q :=
    hf.hasStrictFDerivAt.hasFDerivAt.prodMk hasFDerivAt_snd
  have hb : Function.Bijective (fderiv ℂ (familyEdgeMap f) q) := by
    rw [hder.fderiv]
    apply family_linear_triangular_bijective
    rwa [←family_slice_deriv_eq hf]
  let d : (ℂ × E) ≃L[ℂ] (ℂ × E) := ContinuousLinearEquiv.ofBijective
    (fderiv ℂ (familyEdgeMap f) q) (LinearMap.ker_eq_bot.mpr hb.1)
    (LinearMap.range_eq_top.mpr hb.2)
  have hdF : HasStrictFDerivAt (familyEdgeMap f) (d : (ℂ × E) →L[ℂ] (ℂ × E)) q :=
    hF.hasStrictFDerivAt
  let e := hdF.toOpenPartialHomeomorph (familyEdgeMap f)
  have he : (e : (ℂ × E)→(ℂ × E))=familyEdgeMap f := rfl
  have hq : q∈e.source := hdF.mem_toOpenPartialHomeomorph_source
  refine ⟨e,hq,he,?_⟩
  have ha : AnalyticAt ℂ e q := by rwa [he]
  rcases ha with ⟨ps,hps⟩
  have hp1 : ps 1=(continuousMultilinearCurryFin1 ℂ (ℂ × E) (ℂ × E)).symm
      (d : (ℂ × E) →L[ℂ] (ℂ × E)) := by
    apply (continuousMultilinearCurryFin1 ℂ (ℂ × E) (ℂ × E)).injective
    rw [LinearIsometryEquiv.apply_symm_apply]
    have hd' : HasFDerivAt (e : (ℂ × E)→(ℂ × E))
        (d : (ℂ × E) →L[ℂ] (ℂ × E)) q := by
      rw [he]
      exact hdF.hasFDerivAt
    exact hps.hasFDerivAt.unique hd'
  simpa only [he] using (e.hasFPowerSeriesAt_symm hq hps hp1).analyticAt

end
end IsingBulk.Joint.Transverse
