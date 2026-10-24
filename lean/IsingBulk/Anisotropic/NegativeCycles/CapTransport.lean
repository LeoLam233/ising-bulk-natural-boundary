import IsingBulk.Anisotropic.NegativeCycles.CutoffStokes
import IsingBulk.Anisotropic.NegativeCycles.DensityForm

noncomputable section
namespace IsingBulk.Anisotropic.NegativeCycles
open Set MeasureTheory
open scoped BigOperators

def boxFaceFlux {n : ℕ}
    (ω : ParameterSpace n → ParameterSpace n [⋀^Fin n]→L[ℝ] ℂ)
    (a b : ParameterSpace n) (i : Fin (n+1)) : ℂ :=
  (∫ x in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
      (-1:ℤ)^i.val • ω (i.insertNth (b i) x)
        (i.removeNth (fun k => (Pi.single k (1:ℝ) : ParameterSpace n)))) -
    ∫ x in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
      (-1:ℤ)^i.val • ω (i.insertNth (a i) x)
        (i.removeNth (fun k => (Pi.single k (1:ℝ) : ParameterSpace n)))

def boxCapIntegral {n : ℕ}
    (ω : ParameterSpace n → ParameterSpace n [⋀^Fin n]→L[ℝ] ℂ)
    (a b : ParameterSpace n) (t : ℝ) : ℂ :=
  ∫ x in Icc (a ∘ (0:Fin (n+1)).succAbove) (b ∘ (0:Fin (n+1)).succAbove),
    ω ((0:Fin (n+1)).insertNth t x)
      ((0:Fin (n+1)).removeNth (fun k => (Pi.single k (1:ℝ) : ParameterSpace n)))

theorem boxBoundaryFlux_caps {n : ℕ}
    (ω : ParameterSpace n → ParameterSpace n [⋀^Fin n]→L[ℝ] ℂ)
    (a b : ParameterSpace n) :
    boxBoundaryFlux ω a b=boxCapIntegral ω a b (b 0)-boxCapIntegral ω a b (a 0)+
      ∑ i : Fin n, boxFaceFlux ω a b i.succ := by
  change (∑ i : Fin (n+1), boxFaceFlux ω a b i)=_
  rw [Fin.sum_univ_succ]
  congr 1
  simp [boxFaceFlux,boxCapIntegral]

theorem boxFaceFlux_cutoff_zero {n : ℕ} (χ : ParameterSpace n → ℝ)
    (ω : ParameterSpace n → ParameterSpace n [⋀^Fin n]→L[ℝ] ℂ)
    (a b : ParameterSpace n) (i : Fin (n+1))
    (hfront : ∀q, χ (i.insertNth (b i) q)=0)
    (hback : ∀q, χ (i.insertNth (a i) q)=0) :
    boxFaceFlux (fun x => χ x • ω x) a b i=0 := by
  simp [boxFaceFlux,hfront,hback]

/-- Exact cap comparison with the actual cutoff-boundary integral. -/
theorem cutoff_caps_transport {n : ℕ} {χ : ParameterSpace n → ℝ}
    {ω : ParameterSpace n → ParameterSpace n [⋀^Fin n]→L[ℝ] ℂ}
    (hχ : ContDiff ℝ 1 χ)
    (hω : ∀x∈tsupport χ, DifferentiableAt ℝ ω x)
    (hc : ∀x∈tsupport χ, extDeriv ω x=0)
    {a b : ParameterSpace n} (hab : a≤b)
    (hfront : ∀i : Fin n, ∀q, χ (i.succ.insertNth (b i.succ) q)=0)
    (hback : ∀i : Fin n, ∀q, χ (i.succ.insertNth (a i.succ) q)=0) :
    boxCapIntegral (fun x => χ x • ω x) a b (b 0)-
      boxCapIntegral (fun x => χ x • ω x) a b (a 0)=
        ∫ x in Icc a b, cutoffError χ ω x := by
  have h := cutoff_box_stokes_of_differentiable hχ hω hc hab
  rw [boxBoundaryFlux_caps] at h
  simpa only [boxFaceFlux_cutoff_zero χ ω a b _ (hfront _) (hback _),
    Finset.sum_const_zero,add_zero] using h

/-- Specialization to a genuine complex density and a C² deformation chain. -/
theorem holomorphic_cutoff_caps_transport {n : ℕ}
    {χ : ParameterSpace n → ℝ} (hχ : ContDiff ℝ 1 χ)
    (f : (Fin n → ℂ) → ℂ) (H : ParameterSpace n → Fin n → ℂ)
    (hf : ∀x∈tsupport χ, DifferentiableAt ℂ f (H x))
    (hH : ∀x∈tsupport χ, ContDiffAt ℝ 2 H x)
    {a b : ParameterSpace n} (hab : a≤b)
    (hfront : ∀i : Fin n, ∀q, χ (i.succ.insertNth (b i.succ) q)=0)
    (hback : ∀i : Fin n, ∀q, χ (i.succ.insertNth (a i.succ) q)=0) :
    boxCapIntegral (fun x => χ x • chainPullback (densityForm f) H x) a b (b 0)-
      boxCapIntegral (fun x => χ x • chainPullback (densityForm f) H x) a b (a 0)=
        ∫ x in Icc a b, cutoffError χ (chainPullback (densityForm f) H) x :=
  cutoff_caps_transport hχ
    (fun x hx => chainPullback_differentiableAt (densityForm_differentiableAt (hf x hx)) (hH x hx))
    (fun x hx => chainPullback_closed (densityForm_differentiableAt (hf x hx)) (hH x hx))
    hab hfront hback

end IsingBulk.Anisotropic.NegativeCycles
