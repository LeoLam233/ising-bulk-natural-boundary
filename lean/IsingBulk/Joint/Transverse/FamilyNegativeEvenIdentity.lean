import IsingBulk.Joint.Transverse.FamilyNegativeEvenSide
import IsingBulk.Joint.Transverse.FamilyPhysicalIdentity

/-! # Exact negative-even family transport, including every particle phase -/
namespace IsingBulk.Joint.Transverse
noncomputable section
open IsingBulk.Joint.RegularEdges IsingBulk.Anisotropic.RegularEdges Set Filter Metric
open scoped Topology

def negativeEvenParticleRoot (K : Coupling) : ℂ := Complex.I*S K*Complex.sqrt (-transferB K)
def negativeEvenParticleScale (K : Coupling) : ℂ := Complex.I*S K/negativeEvenParticleRoot K

def negativeEvenLowLeading {E : Type*} (n k : ℕ) (b : ℝ) (curve : ℂ × E→Coupling) (eta : E) : ℂ :=
  FormFactors.lowPrefactor (curve (0,eta))*edgeCoefficientLeading n k b
    (fun u=> -transferB (curve (u,eta))) (fun u=>negativeEvenParticleScale (curve (u,eta)))

theorem negativeEvenParticleRoot_sq (K : Coupling) : negativeEvenParticleRoot K^2=p K := by
  unfold negativeEvenParticleRoot
  rw [mul_pow,mul_pow,IsingBulk.Branch.sqrt_sq,Complex.I_sq]
  unfold transferB p
  by_cases hs : S K=0
  · simp [hs]
  · field_simp

theorem negativeEvenParticleRoot_ne_zero {K : Coupling} (hS : S K≠0)
    (hB : 0<(-transferB K).im) : negativeEvenParticleRoot K≠0 := by
  apply mul_ne_zero (mul_ne_zero Complex.I_ne_zero hS)
  intro hz
  have hh := IsingBulk.Branch.sqrt_sq (-transferB K)
  rw [hz,zero_pow (by decide : 2≠0)] at hh
  rw [←hh,Complex.zero_im] at hB
  exact lt_irrefl _ hB

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem negativeEvenParticleRoot_family_analyticAt {curve : E→Coupling} {x : E}
    (hc : AnalyticAt ℂ curve x) (hS : S (curve x)≠0)
    (hB : 0<(-transferB (curve x)).im) :
    AnalyticAt ℂ (fun x=>negativeEvenParticleRoot (curve x)) x := by
  have hb : -transferB (curve x)∈Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inr (ne_of_gt hB))
  exact (analyticAt_const.mul (Complex.analyticAt_sinh.comp (analyticAt_fst.comp hc))).mul
    ((Complex.differentiableOn_sqrt.analyticOnNhd Complex.isOpen_slitPlane _ hb).comp
      (f := fun x=> -transferB (curve x)) (transferB_family_analyticAt (curve:=curve) hc hS).neg)

theorem negativeEvenParticleScale_family_analyticAt {curve : E→Coupling} {x : E}
    (hc : AnalyticAt ℂ curve x) (hS : S (curve x)≠0)
    (hB : 0<(-transferB (curve x)).im) :
    AnalyticAt ℂ (fun x=>negativeEvenParticleScale (curve x)) x :=
  (analyticAt_const.mul (Complex.analyticAt_sinh.comp (analyticAt_fst.comp hc))).div
    (negativeEvenParticleRoot_family_analyticAt hc hS hB) (negativeEvenParticleRoot_ne_zero hS hB)

/-- Literal LT bulk equals the full even parity series on one common genuine
physical tube. The scale i*S absorbs precisely (-1)^choose(N,2). -/
theorem compact_family_negative_even_low_parity_identity {b : ℝ} (curve : ℂ × E→Coupling)
    {Q : Set E} (hQ : IsCompact Q) (hc : ∀eta∈Q,AnalyticAt ℂ curve (0,eta))
    (hK : ∀eta∈Q,curve (0,eta)∈frontier lowDomain)
    (hS : ∀eta∈Q,S (curve (0,eta))≠0) (hp : ∀eta∈Q,p (curve (0,eta))^2≠1)
    (hB : ∀eta∈Q,0<(-transferB (curve (0,eta))).im) (hb : |b|<1)
    (hn : ∀eta∈Q,∀ᶠu : ℂ in 𝓝 0,negativeParameter b (curve (u,eta))=u) :
    ∃δ : ℝ,0<δ ∧ ∀eta∈Q,∀u : ℂ,‖u‖<δ → 0<u.im →
      FormFactors.lowNormalizedBulk (curve (u,eta))=
        FormFactors.lowPrefactor (curve (u,eta))*paritySeries 1 b
          (fun v=> -transferB (curve (v,eta))) (fun v=>negativeEvenParticleScale (curve (v,eta))) u := by
  obtain ⟨δ,hδ,htube⟩ := compact_family_negative_low_tube curve hQ hc hK hS hp hB hb hn
  refine ⟨δ,hδ,?_⟩
  intro eta heta u hu hi
  obtain ⟨_hc,hS',hB',he,hd⟩ := htube eta heta u hu
  have hdom := hd.mpr hi
  have hfull (n : ℕ) (hn : Even (n+1)) : FormFactors.unscaledFullCoefficient (n+1) (curve (u,eta))=
      angularCoefficient n b (fun v=> -transferB (curve (v,eta)))
        (fun v=>Complex.I*S (curve (v,eta))) u :=
    (fullCoefficient_eq_physicalAngular_low n hdom).trans
      (physicalAngular_eq_negative_even_model (curve:=fun v=>curve (v,eta)) hn
        (lowDomain_subset_spectralComplement hdom) hS' he hi hB')
  have hid : FormFactors.lowNormalizedBulk (curve (u,eta))=
      FormFactors.lowPrefactor (curve (u,eta))*weightedEvenSeries b
        (fun v=> -transferB (curve (v,eta))) (fun v=>Complex.I*S (curve (v,eta)))
        (fun v=>p (curve (v,eta))) u := by
    unfold FormFactors.lowNormalizedBulk weightedEvenSeries
    congr 1
    apply tsum_congr
    intro i
    rw [show 2*i+2=(2*i+1)+1 by omega,hfull (2*i+1) ⟨i+1,by omega⟩]
  rw [hid]
  congr 1
  exact (evenSeries_rescale b (fun v=> -transferB (curve (v,eta)))
    (fun v=>Complex.I*S (curve (v,eta))) (fun v=>negativeEvenParticleRoot (curve (v,eta)))
    (fun v=>p (curve (v,eta))) u (negativeEvenParticleRoot_sq _)).symm

end
end IsingBulk.Joint.Transverse
