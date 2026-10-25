import IsingBulk.Anisotropic.NegativeDominance.PaperParticleAssembly
import IsingBulk.Joint.Negative.ModelData

namespace IsingBulk.Joint.Negative
noncomputable section
open IsingBulk.Anisotropic IsingBulk.Anisotropic.NegativeDominance
open Filter
open scoped Topology BigOperators

/-- Full actual normalized HT coefficient assembly from actual per-particle
estimates. All parity and resonance reindexing and all infinite summability
are discharged here. -/
theorem negative_paper_ranges_of_particle_estimates
    (curve : ℂ→Coupling) (amp B rootB : ℂ→ℂ) (phi : ℝ)
    {p : ℕ} (hp : 0<p) (hpOdd : Odd p)
    {a Dlow aP aR : ℝ} (ha : 0<a) (hDlow : 0≤Dlow) (haP : 0<aP) (haR : 0<aR)
    (CP CR Chigh : ℝ) (eta : ℕ→ℝ) (heta : ∀ᶠj : ℕ in atTop,0≤eta j)
    (hlow : ∀j m,‖negativePaperParticleCoefficient curve amp m j‖≤
      Dlow*((2*m+1 : ℕ) : ℝ)^2*(((2*m+1 : ℕ) : ℝ)^3/a)^j)
    (hnonres : ∀j m,¬p∣2*m+1 → ‖negativePaperParticleCoefficient curve amp m j‖≤gaussianEnvelope aR CR (2*m+1) j)
    (hmiddle : ∀ᶠj : ℕ in atTop,∀m,p∣2*m+1 →
      Real.log j<((2*m+1 : ℕ) : ℝ) → ((2*m+1 : ℕ) : ℝ)^2≤j/Real.sqrt (Real.log j) →
      ‖negativePaperParticleCoefficient curve amp m j-physicalModel B rootB phi (2*m+1) j‖≤
        eta j*‖physicalModel B rootB phi (2*m+1) j‖+gaussianEnvelope aP CP (2*m+1) j)
    (hhigh : ∀ᶠj : ℕ in atTop,∀m,p∣2*m+1 →
      Real.log j<((2*m+1 : ℕ) : ℝ) → (j : ℝ)/Real.sqrt (Real.log j)<((2*m+1 : ℕ) : ℝ)^2 →
      ‖negativePaperParticleCoefficient curve amp m j‖≤
        Real.exp (2*j*Real.log (2*m+1)-((2*m+1 : ℕ) : ℝ)^2/2*Real.log (2*m+1)+Chigh*((2*m+1 : ℕ) : ℝ)^2)+
        gaussianEnvelope aP CP (2*m+1) j) :
    ∃D C : ℝ,0<D ∧ ∀ᶠj : ℕ in atTop,
      HasCoefficientRanges (negativePaperCoefficient curve amp) B rootB phi p a D C eta j := by
  classical
  let coeff := fun j=>oddCoefficientLift (fun m=>negativePaperParticleCoefficient curve amp m j)
  let ag := min aP aR
  let cg := max CP CR
  have hag : 0<ag := lt_min haP haR
  have hleft (N j : ℕ) := gaussianEnvelope_mono (min_le_left aP aR) (le_max_left CP CR) N j
  have hright (N j : ℕ) := gaussianEnvelope_mono (min_le_right aP aR) (le_max_right CP CR) N j
  have heven : ∀j N,¬Odd N → coeff j N=0 := by
    intro j N hn
    exact ite_eq_right hn
  have hlo : ∀j N,Odd N → ‖coeff j N‖≤Dlow*(N : ℝ)^2*((N : ℝ)^3/a)^j := by
    intro j N hn
    obtain ⟨m,rfl⟩ := hn
    simpa only [coeff,oddCoefficientLift_odd] using hlow j m
  have hnr : ∀j N,Odd N → ¬p∣N → ‖coeff j N‖≤gaussianEnvelope ag cg N j := by
    intro j N hn hnd
    obtain ⟨m,rfl⟩ := hn
    simpa only [coeff,oddCoefficientLift_odd] using (hnonres j m hnd).trans (hright (2*m+1) j)
  have hm : ∀ᶠj : ℕ in atTop,∀N,N∈(resonantMiddleIndices p j).image (resonantParticle p) →
      ‖coeff j N-particleMiddleModel B rootB phi p j N‖≤
        eta j*‖particleMiddleModel B rootB phi p j N‖+gaussianEnvelope ag cg N j := by
    filter_upwards [hmiddle] with j hj
    intro N hN
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hN
    have ho : Odd (resonantParticle p i) := hpOdd.mul ⟨i,rfl⟩
    obtain ⟨m,hm⟩ := ho
    have hd : p∣2*m+1 := by rw [←hm]; exact dvd_mul_right p _
    have hcut := (Finset.mem_filter.mp hi).2
    rw [hm] at hcut
    have hh := (hj m hd hcut.1 hcut.2).trans
      (add_le_add (le_refl _) (hleft (2*m+1) j))
    rw [particleMiddleModel_at B rootB phi hp,ite_eq_left hi,hm]
    simpa only [coeff,oddCoefficientLift_odd] using hh
  have hh : ∀ᶠj : ℕ in atTop,∀N : ℕ,Odd N → p∣N → Real.log j<(N : ℝ) →
      (j : ℝ)/Real.sqrt (Real.log j)<(N : ℝ)^2 →
      ‖coeff j N‖≤Real.exp (2*j*Real.log N-(N : ℝ)^2/2*Real.log N+Chigh*(N : ℝ)^2)+gaussianEnvelope ag cg N j := by
    filter_upwards [hhigh] with j hj
    intro N hn hd hlo hhi
    obtain ⟨m,rfl⟩ := hn
    have h := (hj m hd hlo hhi).trans (add_le_add (le_refl _) (hleft (2*m+1) j))
    simpa only [coeff,oddCoefficientLift_odd,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] using h
  obtain ⟨D,C,hD,hout⟩ := particle_estimates_eventual_ranges B rootB phi hp hpOdd ha hDlow hag cg Chigh coeff eta heta heven hlo hnr hm hh
  refine ⟨D,C,hD,?_⟩
  filter_upwards [hout] with j hj
  have hf : Summable (fun m=>negativePaperParticleCoefficient curve amp m j) := by
    have hi : Function.Injective (fun m : ℕ=>2*m+1) := by intro x y h; dsimp only at h; omega
    simpa only [coeff,Function.comp_def,oddCoefficientLift_odd] using hj.1.comp_injective hi
  have he := negativePaperCoefficient_eq_oddLift hf
  change HasCoefficientRanges _ _ _ _ _ _ _ _ _ _
  unfold HasCoefficientRanges at hj ⊢
  simpa only [he,coeff] using hj.2

end
end IsingBulk.Joint.Negative
