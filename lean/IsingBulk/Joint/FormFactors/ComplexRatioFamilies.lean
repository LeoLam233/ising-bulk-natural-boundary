import IsingBulk.Joint.FormFactors.ComplexRatio
import IsingBulk.Joint.RegularEdges.BoundaryPrefactors

/-! The analytic implicit family of Lemma 7.1 with actual scale, anisotropy,
physical prefactor, and common strict margins. The family is constructed here;
none of its analytic or admissibility properties is a supplied conclusion. -/
namespace IsingBulk.Joint.FormFactors
noncomputable section
open Set Filter Metric
open scoped Topology

/-- Data of the constructed actual complex-ratio family on a doubled closed
polydisk. The smaller disk is reserved for uniform Cauchy estimates. -/
structure ComplexRatioFamily (edge amp : Coupling → ℂ) (sign : ℝ) (z₀ lam₀ : ℂ) where
  temperature : Coupling → ℂ
  coupling : Coupling → Coupling
  radius : ℝ
  radius_pos : 0<radius
  coupling_eq : coupling=fun q => complexRatioMap (temperature q,q.2)
  temperature_zero : temperature (0,lam₀)=z₀
  coupling_zero : coupling (0,lam₀)=(z₀,lam₀*z₀)
  temperature_analytic : ∀ u lam : ℂ, ‖u‖≤2*radius → ‖lam-lam₀‖≤2*radius →
    AnalyticAt ℂ temperature (u,lam)
  coupling_analytic : ∀ u lam : ℂ, ‖u‖≤2*radius → ‖lam-lam₀‖≤2*radius →
    AnalyticAt ℂ coupling (u,lam)
  edge_eq : ∀ u lam : ℂ, ‖u‖≤2*radius → ‖lam-lam₀‖≤2*radius → edge (coupling (u,lam))=u
  anisotropy_analytic : ∀ u lam : ℂ, ‖u‖≤2*radius → ‖lam-lam₀‖≤2*radius →
    AnalyticAt ℂ (fun q => transferB (coupling q)) (u,lam)
  scale_analytic : ∀ u lam : ℂ, ‖u‖≤2*radius → ‖lam-lam₀‖≤2*radius →
    AnalyticAt ℂ (fun q => S (coupling q)) (u,lam)
  prefactor_analytic : ∀ u lam : ℂ, ‖u‖≤2*radius → ‖lam-lam₀‖≤2*radius →
    AnalyticAt ℂ (fun q => amp (coupling q)) (u,lam)
  anisotropy_margin : ∀ u lam : ℂ, ‖u‖≤2*radius → ‖lam-lam₀‖≤2*radius →
    sign*(transferB (z₀,lam₀*z₀)).im/2 < sign*(transferB (coupling (u,lam))).im
  scale_margin : ∀ u lam : ℂ, ‖u‖≤2*radius → ‖lam-lam₀‖≤2*radius →
    ‖S (z₀,lam₀*z₀)‖/2 < ‖S (coupling (u,lam))‖
  prefactor_margin : ∀ u lam : ℂ, ‖u‖≤2*radius → ‖lam-lam₀‖≤2*radius →
    ‖amp (z₀,lam₀*z₀)‖/2 < ‖amp (coupling (u,lam))‖
  inverse : ∀ᶠ q : Coupling in 𝓝 (z₀,lam₀), temperature (edge (complexRatioMap q),q.2)=q.1

/-- All complex parameters share a single polydisk and quantitative nonzero
margins. This construction uses the genuine joint implicit-function theorem. -/
theorem exists_admissible_complex_ratio_family {edge amp : Coupling → ℂ}
    {sign : ℝ} {z₀ lam₀ : ℂ}
    (he : AnalyticAt ℂ edge (z₀,lam₀*z₀)) (he0 : edge (z₀,lam₀*z₀)=0)
    (hd : deriv (fun z => edge (z,lam₀*z)) z₀≠0)
    (hS : S (z₀,lam₀*z₀)≠0) (hB : 0<sign*(transferB (z₀,lam₀*z₀)).im)
    (ha : AnalyticAt ℂ amp (z₀,lam₀*z₀)) (ha0 : amp (z₀,lam₀*z₀)≠0) :
    Nonempty (ComplexRatioFamily edge amp sign z₀ lam₀) := by
  let K : Coupling := (z₀,lam₀*z₀)
  have hSa : AnalyticAt ℂ S K := Complex.analyticAt_sinh.comp analyticAt_fst
  have hBa : AnalyticAt ℂ transferB K := transferB_analyticAt hS
  have hspos : 0<‖S K‖ := norm_pos_iff.mpr hS
  have hapos : 0<‖amp K‖ := norm_pos_iff.mpr ha0
  have hevent : ∀ᶠ L in 𝓝 K,
      S L≠0 ∧ AnalyticAt ℂ amp L ∧
      sign*(transferB K).im/2<sign*(transferB L).im ∧
      ‖S K‖/2<‖S L‖ ∧ ‖amp K‖/2<‖amp L‖ := by
    have hbc : ContinuousAt (fun L : Coupling => sign*(transferB L).im) K :=
      continuousAt_const.mul (Complex.continuous_im.continuousAt.comp hBa.continuousAt)
    have hb := continuousAt_const.eventually_lt hbc
      (by change sign*(transferB K).im/2<sign*(transferB K).im; linarith)
    exact (hSa.continuousAt.eventually_ne hS).and
      (ha.eventually_analyticAt.and (hb.and
        ((continuousAt_const.eventually_lt hSa.continuousAt.norm (by linarith)).and
          (continuousAt_const.eventually_lt ha.continuousAt.norm (by linarith)))))
  obtain ⟨V,hVsub,hV,hKV⟩ := _root_.mem_nhds_iff.mp hevent
  obtain ⟨Z,f,r,hr,hf,hZ0,hf0,hdata,hinv⟩ :=
    exists_complex_ratio_edge_polydisk he he0 hd hV hKV
  refine ⟨⟨Z,f,r,hr,hf,hZ0,hf0,
    (fun u l hu hl => (hdata u l hu hl).1),
    (fun u l hu hl => (hdata u l hu hl).2.1),
    (fun u l hu hl => (hdata u l hu hl).2.2.1),
    ?_,?_,?_,?_,?_,?_,hinv⟩⟩
  · intro u l hu hl
    exact (transferB_analyticAt (hVsub (hdata u l hu hl).2.2.2).1).comp (hdata u l hu hl).2.1
  · intro u l hu hl
    exact (Complex.analyticAt_sinh.comp analyticAt_fst).comp (hdata u l hu hl).2.1
  · intro u l hu hl
    exact (hVsub (hdata u l hu hl).2.2.2).2.1.comp (hdata u l hu hl).2.1
  · intro u l hu hl
    exact (hVsub (hdata u l hu hl).2.2.2).2.2.1
  · intro u l hu hl
    exact (hVsub (hdata u l hu hl).2.2.2).2.2.2.1
  · intro u l hu hl
    exact (hVsub (hdata u l hu hl).2.2.2).2.2.2.2

theorem positive_edge_analyticAt (b : ℂ) {K : Coupling} (hS : S K≠0) :
    AnalyticAt ℂ (Transverse.positiveParameter b) K :=
  ((transferC_analyticAt hS).sub (transferB_analyticAt hS)).sub analyticAt_const

theorem negative_edge_analyticAt (b : ℂ) {K : Coupling}
    (hS : S K≠0) (hB : transferB K≠0) :
    AnalyticAt ℂ (Negative.edgeParameter b) K :=
  (((transferC_analyticAt hS).add (transferB_analyticAt hS)).sub analyticAt_const).div
    (transferB_analyticAt hS) hB

/-- Positive-edge actual complex ratio family; the physical amplitude may be
the actual HT or LT prefactor, whose boundary analyticity is proved separately. -/
theorem positive_complex_ratio_family {b z₀ lam₀ : ℂ} {amp : Coupling → ℂ}
    (hS : S (z₀,lam₀*z₀)≠0) (hB : 0<(transferB (z₀,lam₀*z₀)).im)
    (he0 : Transverse.positiveParameter b (z₀,lam₀*z₀)=0)
    (hd : deriv (fun z => Transverse.positiveParameter b (z,lam₀*z)) z₀≠0)
    (ha : AnalyticAt ℂ amp (z₀,lam₀*z₀)) (ha0 : amp (z₀,lam₀*z₀)≠0) :
    Nonempty (ComplexRatioFamily (Transverse.positiveParameter b) amp 1 z₀ lam₀) :=
  exists_admissible_complex_ratio_family (positive_edge_analyticAt b hS) he0 hd hS
    (by simpa using hB) ha ha0

/-- Negative-edge family uses the scaled parameter t=(C+B-b)/B, exactly the
one used by the all-index negative normal form, with genuinely varying B. -/
theorem negative_complex_ratio_family {b z₀ lam₀ : ℂ} {amp : Coupling → ℂ}
    (hS : S (z₀,lam₀*z₀)≠0) (hB : (transferB (z₀,lam₀*z₀)).im<0)
    (he0 : Negative.edgeParameter b (z₀,lam₀*z₀)=0)
    (hd : deriv (fun z => Negative.edgeParameter b (z,lam₀*z)) z₀≠0)
    (ha : AnalyticAt ℂ amp (z₀,lam₀*z₀)) (ha0 : amp (z₀,lam₀*z₀)≠0) :
    Nonempty (ComplexRatioFamily (Negative.edgeParameter b) amp (-1) z₀ lam₀) :=
  exists_admissible_complex_ratio_family
    (negative_edge_analyticAt b hS (Negative.transferB_ne_zero_of_im_neg hB)) he0 hd hS
    (by simpa using hB) ha ha0

/-- All physical prefactor hypotheses are discharged at an actual noncritical
high-temperature boundary point. -/
theorem positive_high_complex_ratio_family {b z₀ lam₀ : ℂ}
    (hK : (z₀,lam₀*z₀)∈closure highDomain) (hp : p (z₀,lam₀*z₀)^2≠1)
    (hS : S (z₀,lam₀*z₀)≠0) (hB : 0<(transferB (z₀,lam₀*z₀)).im)
    (he0 : Transverse.positiveParameter b (z₀,lam₀*z₀)=0)
    (hd : deriv (fun z => Transverse.positiveParameter b (z,lam₀*z)) z₀≠0) :
    Nonempty (ComplexRatioFamily (Transverse.positiveParameter b) highPrefactor 1 z₀ lam₀) :=
  positive_complex_ratio_family hS hB he0 hd
    (RegularEdges.highPrefactor_boundary_analyticAt hK hp) (highPrefactor_ne_zero _)

theorem positive_low_complex_ratio_family {b z₀ lam₀ : ℂ}
    (hK : (z₀,lam₀*z₀)∈closure lowDomain) (hp : p (z₀,lam₀*z₀)^2≠1)
    (hS : S (z₀,lam₀*z₀)≠0) (hB : 0<(transferB (z₀,lam₀*z₀)).im)
    (he0 : Transverse.positiveParameter b (z₀,lam₀*z₀)=0)
    (hd : deriv (fun z => Transverse.positiveParameter b (z,lam₀*z)) z₀≠0) :
    Nonempty (ComplexRatioFamily (Transverse.positiveParameter b) lowPrefactor 1 z₀ lam₀) :=
  positive_complex_ratio_family hS hB he0 hd
    (RegularEdges.lowPrefactor_boundary_analyticAt hK hp) (lowPrefactor_ne_zero _)

theorem negative_high_complex_ratio_family {b z₀ lam₀ : ℂ}
    (hK : (z₀,lam₀*z₀)∈closure highDomain) (hp : p (z₀,lam₀*z₀)^2≠1)
    (hS : S (z₀,lam₀*z₀)≠0) (hB : (transferB (z₀,lam₀*z₀)).im<0)
    (he0 : Negative.edgeParameter b (z₀,lam₀*z₀)=0)
    (hd : deriv (fun z => Negative.edgeParameter b (z,lam₀*z)) z₀≠0) :
    Nonempty (ComplexRatioFamily (Negative.edgeParameter b) highPrefactor (-1) z₀ lam₀) :=
  negative_complex_ratio_family hS hB he0 hd
    (RegularEdges.highPrefactor_boundary_analyticAt hK hp) (highPrefactor_ne_zero _)

theorem negative_low_complex_ratio_family {b z₀ lam₀ : ℂ}
    (hK : (z₀,lam₀*z₀)∈closure lowDomain) (hp : p (z₀,lam₀*z₀)^2≠1)
    (hS : S (z₀,lam₀*z₀)≠0) (hB : (transferB (z₀,lam₀*z₀)).im<0)
    (he0 : Negative.edgeParameter b (z₀,lam₀*z₀)=0)
    (hd : deriv (fun z => Negative.edgeParameter b (z,lam₀*z)) z₀≠0) :
    Nonempty (ComplexRatioFamily (Negative.edgeParameter b) lowPrefactor (-1) z₀ lam₀) :=
  negative_complex_ratio_family hS hB he0 hd
    (RegularEdges.lowPrefactor_boundary_analyticAt hK hp) (lowPrefactor_ne_zero _)

end
end IsingBulk.Joint.FormFactors
