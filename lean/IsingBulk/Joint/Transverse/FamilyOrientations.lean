import IsingBulk.Joint.Transverse.AnalyticReflection
import IsingBulk.HT.Contour.SignedReflectionJets
import Mathlib.Topology.UniformSpace.UniformConvergence

/-! # Quantitative transport of the actual physical families

Exchange of the lattice axes costs no constant. Schwarz reflection conjugates
both the curve parameter and the complex family parameter. The identities are
identities of the literal normalized bulk jets on their actual physical side,
not identities of independently chosen model coefficients. Thus every common
bound and uniform scaled limit transfers without loss of radius or constant.
-/
namespace IsingBulk.Joint.Transverse
noncomputable section
open Set Filter Metric
open scoped Topology

/-- Exchange the two independent couplings, leaving both parameters unchanged. -/
def swappedFamily {E : Type*} (c : ℂ × E → Coupling) : ℂ × E → Coupling :=
  fun q => (c q).swap

/-- Reflect the actual holomorphic family, including its family parameter. -/
def reflectedFamily {E : Type*} [Star E] (c : ℂ × E → Coupling) : ℂ × E → Coupling :=
  fun q => star (c (star q))

theorem swappedFamily_analyticAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {c : ℂ × E → Coupling} {q : ℂ × E} (hc : AnalyticAt ℂ c q) :
    AnalyticAt ℂ (swappedFamily c) q := (analyticAt_snd.comp hc).prod (analyticAt_fst.comp hc)

theorem reflectedFamily_analyticAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [StarAddMonoid E] [StarModule ℂ E] [NormedStarGroup E]
    {c : ℂ × E → Coupling} {q : ℂ × E}
    (hc : AnalyticAt ℂ c q) : AnalyticAt ℂ (reflectedFamily c) (star q) := by
  let : NormedStarGroup (ℂ × E) := ⟨fun x => by simp [Prod.norm_def,Prod.star_def]⟩
  exact analyticAt_star_star hc

/-- Joint holomorphy of the reflected family is genuine complex
Fréchet differentiability, not antiholomorphy of its source parameter. -/
theorem reflectedFamily_differentiableAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [StarAddMonoid E] [StarModule ℂ E] [NormedStarGroup E]
    {c : ℂ × E → Coupling} {q : ℂ × E}
    (hc : DifferentiableAt ℂ c q) :
    DifferentiableAt ℂ (reflectedFamily c) (star q) := by
  change DifferentiableAt ℂ (star ∘ c ∘ star) (star q)
  exact hc.star_star

theorem reflectedFamily_fiber_analyticAt {E : Type*} [InvolutiveStar E]
    {c : ℂ × E → Coupling} {u : ℂ} {eta : E}
    (hc : AnalyticAt ℂ (fun z => c (z,eta)) u) :
    AnalyticAt ℂ (fun z => reflectedFamily c (z,star eta)) (star u) := by
  convert! reflectedCurve_analyticAt hc using 1
  ext z <;> simp [reflectedFamily,reflectedCurve,Prod.star_def]

theorem isCompact_reflected_parameters {E : Type*} [TopologicalSpace E]
    [InvolutiveStar E] [ContinuousStar E] {Q : Set E} (hQ : IsCompact Q) :
    IsCompact (star ⁻¹' Q) := by
  have he : star ⁻¹' Q = star '' Q := by
    ext z
    constructor
    · intro hz
      exact ⟨star z,hz,star_star z⟩
    · rintro ⟨w,hw,rfl⟩
      simpa using hw
  rw [he]
  exact hQ.image continuous_star

/-- The actual local domain supplies the germ equality before differentiation. -/
theorem iteratedDeriv_swapped_curve {D : Set Coupling} {f : Coupling → ℂ}
    (hD : IsOpen D) (hf : ∀ K∈D, f K.swap=f K)
    {c : ℂ → Coupling} {u : ℂ} (hc : ContinuousAt c u) (hu : c u∈D) (j : ℕ) :
    iteratedDeriv j (fun z => f (c z).swap) u = iteratedDeriv j (f ∘ c) u := by
  have he : (fun z => f (c z).swap) =ᶠ[𝓝 u] f ∘ c := by
    filter_upwards [hc.preimage_mem_nhds (hD.mem_nhds hu)] with z hz
    exact hf (c z) hz
  exact he.iteratedDeriv_eq j

/-- The parameter derivative is conjugated, with no spurious sign or phase. -/
theorem iteratedDeriv_reflected_curve {D : Set Coupling} {f : Coupling → ℂ}
    (hD : IsOpen D) (hf : ∀ K∈D, f (star K)=star (f K))
    {c : ℂ → Coupling} {u : ℂ} (hc : ContinuousAt c u) (hu : c u∈D) (j : ℕ) :
    iteratedDeriv j (f ∘ reflectedCurve c) (star u) = star (iteratedDeriv j (f ∘ c) u) := by
  have hs : Tendsto (star : ℂ→ℂ) (𝓝 (star u)) (𝓝 u) := by
    simpa using continuous_star.tendsto (star u)
  have he : f ∘ reflectedCurve c =ᶠ[𝓝 (star u)] star ∘ (f ∘ c) ∘ star := by
    filter_upwards [hs.eventually (hc.preimage_mem_nhds (hD.mem_nhds hu))] with z hz
    exact hf (c (star z)) hz
  rw [he.iteratedDeriv_eq j,IsingBulk.HT.Contour.iteratedDeriv_star_conj]
  simp only [Function.comp_def,star_star]

theorem iteratedDeriv_reflected_curve_norm {D : Set Coupling} {f : Coupling → ℂ}
    (hD : IsOpen D) (hf : ∀ K∈D, f (star K)=star (f K))
    {c : ℂ → Coupling} {u : ℂ} (hc : ContinuousAt c u) (hu : c u∈D) (j : ℕ) :
    ‖iteratedDeriv j (f ∘ reflectedCurve c) (star u)‖ = ‖iteratedDeriv j (f ∘ c) u‖ := by
  rw [iteratedDeriv_reflected_curve hD hf hc hu j,norm_star]

/-- Uniform convergence survives reflection of a complex parameter set. This
holds for arbitrary sets, so in particular for every compact family. -/
theorem uniform_reflected_parameters {I E : Type*} [Star E] {l : Filter I}
    {F : I → E → ℂ} {G : E → ℂ} {Q : Set E}
    (h : TendstoUniformlyOn F G l Q) :
    TendstoUniformlyOn (fun t eta => star (F t (star eta)))
      (fun eta => star (G (star eta))) l (star ⁻¹' Q) := by
  rw [Metric.tendstoUniformlyOn_iff] at h ⊢
  intro ε hε
  filter_upwards [h ε hε] with t ht eta heta
  simpa only [dist_eq_norm,←star_sub,norm_star] using ht (star eta) heta

/-- Common scaled jet asymptotics for exchanged axes. The sole geometric
input is the actual common physical side along the approach path. -/
theorem uniform_scaled_jets_swapped {I E : Type*} {l : Filter I}
    {D : Set Coupling} {f : Coupling → ℂ} (hD : IsOpen D)
    (hf : ∀ K∈D, f K.swap=f K) {c : ℂ × E → Coupling}
    {Q : Set E} {w : I → ℂ} {r : I → ℂ} {G : E → ℂ} (j : ℕ)
    (hc : ∀ᶠt in l, ∀eta∈Q,
      ContinuousAt (fun z => c (z,eta)) (w t) ∧ c (w t,eta)∈D)
    (h : TendstoUniformlyOn
      (fun t eta => r t*iteratedDeriv j (fun z => f (c (z,eta))) (w t)) G l Q) :
    TendstoUniformlyOn
      (fun t eta => r t*iteratedDeriv j (fun z => f (swappedFamily c (z,eta))) (w t)) G l Q := by
  apply h.congr
  filter_upwards [hc] with t ht eta heta
  dsimp only
  rw [show iteratedDeriv j (fun z => f (swappedFamily c (z,eta))) (w t) =
      iteratedDeriv j (fun z => f (c (z,eta))) (w t) from
    iteratedDeriv_swapped_curve hD hf (ht eta heta).1 (ht eta heta).2 j]

/-- Reflection sends a scaled asymptotic to its conjugate. Both parameters
are reflected and the entire complex scale is conjugated, so this also
covers phase-sensitive asymptotic constants. -/
theorem uniform_scaled_jets_reflected {I E : Type*} [Star E] {l : Filter I}
    {D : Set Coupling} {f : Coupling → ℂ} (hD : IsOpen D)
    (hf : ∀ K∈D, f (star K)=star (f K)) {c : ℂ × E → Coupling}
    {Q : Set E} {w : I → ℂ} {r : I → ℂ} {G : E → ℂ} (j : ℕ)
    (hc : ∀ᶠt in l, ∀eta∈Q,
      ContinuousAt (fun z => c (z,eta)) (w t) ∧ c (w t,eta)∈D)
    (h : TendstoUniformlyOn
      (fun t eta => r t*iteratedDeriv j (fun z => f (c (z,eta))) (w t)) G l Q) :
    TendstoUniformlyOn
      (fun t eta => star (r t)*iteratedDeriv j
        (fun z => f (reflectedFamily c (z,eta))) (star (w t)))
      (fun eta => star (G (star eta))) l (star ⁻¹' Q) := by
  apply (uniform_reflected_parameters h).congr
  filter_upwards [hc] with t ht eta heta
  have he := iteratedDeriv_reflected_curve hD hf (ht (star eta) heta).1
    (ht (star eta) heta).2 j
  change _ = star (r t)*iteratedDeriv j (f ∘ reflectedCurve (fun z => c (z,star eta))) (star (w t))
  rw [he]
  simp only [Function.comp_def,star_mul']

/-- Exact jet identities for the actual high-temperature susceptibility. -/
theorem highNormalizedBulk_swapped_jet {c : ℂ → Coupling} {u : ℂ}
    (hc : ContinuousAt c u) (hu : c u∈highDomain) (j : ℕ) :
    iteratedDeriv j (fun z => FormFactors.highNormalizedBulk (c z).swap) u =
      iteratedDeriv j (FormFactors.highNormalizedBulk ∘ c) u :=
  iteratedDeriv_swapped_curve highDomain_isOpen (fun _ hK => FormFactors.highNormalizedBulk_swap hK) hc hu j

theorem lowNormalizedBulk_swapped_jet {c : ℂ → Coupling} {u : ℂ}
    (hc : ContinuousAt c u) (hu : c u∈lowDomain) (j : ℕ) :
    iteratedDeriv j (fun z => FormFactors.lowNormalizedBulk (c z).swap) u =
      iteratedDeriv j (FormFactors.lowNormalizedBulk ∘ c) u :=
  iteratedDeriv_swapped_curve lowDomain_isOpen (fun _ hK => FormFactors.lowNormalizedBulk_swap hK) hc hu j

variable {corrH corrL : PhysicalField.CorrelationFamily}

theorem highNormalizedBulk_reflected_jet
    (hphys : PhysicalField.PublishedRealSpinFamily corrH corrL)
    {c : ℂ → Coupling} {u : ℂ} (hc : ContinuousAt c u) (hu : c u∈highDomain) (j : ℕ) :
    iteratedDeriv j (FormFactors.highNormalizedBulk ∘ reflectedCurve c) (star u) =
      star (iteratedDeriv j (FormFactors.highNormalizedBulk ∘ c) u) :=
  iteratedDeriv_reflected_curve highDomain_isOpen
    (fun _ hK => FormFactors.highNormalizedBulk_conjugate hphys hK) hc hu j

theorem lowNormalizedBulk_reflected_jet
    (hphys : PhysicalField.PublishedRealSpinFamily corrH corrL)
    {c : ℂ → Coupling} {u : ℂ} (hc : ContinuousAt c u) (hu : c u∈lowDomain) (j : ℕ) :
    iteratedDeriv j (FormFactors.lowNormalizedBulk ∘ reflectedCurve c) (star u) =
      star (iteratedDeriv j (FormFactors.lowNormalizedBulk ∘ c) u) :=
  iteratedDeriv_reflected_curve lowDomain_isOpen
    (fun _ hK => FormFactors.lowNormalizedBulk_conjugate hphys hK) hc hu j

/-- Reflection preserves the radius of an actual complex parameter disk. -/
theorem reflected_closedBall {E : Type*} [NormedAddCommGroup E]
    [StarAddMonoid E] [NormedStarGroup E] (eta₀ : E) (r : ℝ) :
    star ⁻¹' closedBall eta₀ r = closedBall (star eta₀) r := by
  ext eta
  simp only [mem_preimage,mem_closedBall,dist_eq_norm]
  have he : ‖star eta-eta₀‖=‖eta-star eta₀‖ := by
    calc
      _ = ‖star (eta-star eta₀)‖ := by simp only [star_sub,star_star]
      _ = _ := norm_star _
  rw [he]

@[simp] theorem swappedFamily_high_iff {E : Type*} (c : ℂ × E → Coupling) (q : ℂ × E) :
    swappedFamily c q∈highDomain ↔ c q∈highDomain := swap_highDomain_iff _

@[simp] theorem swappedFamily_low_iff {E : Type*} (c : ℂ × E → Coupling) (q : ℂ × E) :
    swappedFamily c q∈lowDomain ↔ c q∈lowDomain := swap_lowDomain_iff _

@[simp] theorem reflectedFamily_high_iff {E : Type*} [Star E] (c : ℂ × E → Coupling) (q : ℂ × E) :
    reflectedFamily c q∈highDomain ↔ c (star q)∈highDomain :=
  FormFactors.star_mem_highDomain_iff _

@[simp] theorem reflectedFamily_low_iff {E : Type*} [Star E] (c : ℂ × E → Coupling) (q : ℂ × E) :
    reflectedFamily c q∈lowDomain ↔ c (star q)∈lowDomain :=
  FormFactors.star_mem_lowDomain_iff _

theorem highNormalizedBulk_uniform_scaled_swapped {I E : Type*} {l : Filter I}
    {c : ℂ × E → Coupling} {Q : Set E} {w : I → ℂ} {r : I → ℂ} {G : E → ℂ} (j : ℕ)
    (hc : ∀ᶠt in l, ∀eta∈Q,
      ContinuousAt (fun z => c (z,eta)) (w t) ∧ c (w t,eta)∈highDomain)
    (h : TendstoUniformlyOn (fun t eta => r t*iteratedDeriv j
      (fun z => FormFactors.highNormalizedBulk (c (z,eta))) (w t)) G l Q) :
    TendstoUniformlyOn (fun t eta => r t*iteratedDeriv j
      (fun z => FormFactors.highNormalizedBulk (swappedFamily c (z,eta))) (w t)) G l Q :=
  uniform_scaled_jets_swapped highDomain_isOpen
    (fun _ hK => FormFactors.highNormalizedBulk_swap hK) j hc h

theorem lowNormalizedBulk_uniform_scaled_swapped {I E : Type*} {l : Filter I}
    {c : ℂ × E → Coupling} {Q : Set E} {w : I → ℂ} {r : I → ℂ} {G : E → ℂ} (j : ℕ)
    (hc : ∀ᶠt in l, ∀eta∈Q,
      ContinuousAt (fun z => c (z,eta)) (w t) ∧ c (w t,eta)∈lowDomain)
    (h : TendstoUniformlyOn (fun t eta => r t*iteratedDeriv j
      (fun z => FormFactors.lowNormalizedBulk (c (z,eta))) (w t)) G l Q) :
    TendstoUniformlyOn (fun t eta => r t*iteratedDeriv j
      (fun z => FormFactors.lowNormalizedBulk (swappedFamily c (z,eta))) (w t)) G l Q :=
  uniform_scaled_jets_swapped lowDomain_isOpen
    (fun _ hK => FormFactors.lowNormalizedBulk_swap hK) j hc h

theorem highNormalizedBulk_uniform_scaled_reflected {I E : Type*} [Star E] {l : Filter I}
    (hphys : PhysicalField.PublishedRealSpinFamily corrH corrL)
    {c : ℂ × E → Coupling} {Q : Set E} {w : I → ℂ} {r : I → ℂ} {G : E → ℂ} (j : ℕ)
    (hc : ∀ᶠt in l, ∀eta∈Q,
      ContinuousAt (fun z => c (z,eta)) (w t) ∧ c (w t,eta)∈highDomain)
    (h : TendstoUniformlyOn (fun t eta => r t*iteratedDeriv j
      (fun z => FormFactors.highNormalizedBulk (c (z,eta))) (w t)) G l Q) :
    TendstoUniformlyOn (fun t eta => star (r t)*iteratedDeriv j
      (fun z => FormFactors.highNormalizedBulk (reflectedFamily c (z,eta))) (star (w t)))
      (fun eta => star (G (star eta))) l (star ⁻¹' Q) :=
  uniform_scaled_jets_reflected highDomain_isOpen
    (fun _ hK => FormFactors.highNormalizedBulk_conjugate hphys hK) j hc h

theorem lowNormalizedBulk_uniform_scaled_reflected {I E : Type*} [Star E] {l : Filter I}
    (hphys : PhysicalField.PublishedRealSpinFamily corrH corrL)
    {c : ℂ × E → Coupling} {Q : Set E} {w : I → ℂ} {r : I → ℂ} {G : E → ℂ} (j : ℕ)
    (hc : ∀ᶠt in l, ∀eta∈Q,
      ContinuousAt (fun z => c (z,eta)) (w t) ∧ c (w t,eta)∈lowDomain)
    (h : TendstoUniformlyOn (fun t eta => r t*iteratedDeriv j
      (fun z => FormFactors.lowNormalizedBulk (c (z,eta))) (w t)) G l Q) :
    TendstoUniformlyOn (fun t eta => star (r t)*iteratedDeriv j
      (fun z => FormFactors.lowNormalizedBulk (reflectedFamily c (z,eta))) (star (w t)))
      (fun eta => star (G (star eta))) l (star ⁻¹' Q) :=
  uniform_scaled_jets_reflected lowDomain_isOpen
    (fun _ hK => FormFactors.lowNormalizedBulk_conjugate hphys hK) j hc h

end
end IsingBulk.Joint.Transverse
