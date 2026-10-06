import IsingBulk.Tail.WeightedAngularJets
import IsingBulk.Tail.SelectorPeriodicity
import IsingBulk.First.PeriodicBoxIntegral

/-! Exact signed fundamental-domain transfer for the actual fixed-weight
angular jets. Both complex integrals and their absolute majorants transfer. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First MeasureTheory Set Filter
open scoped Topology

def signedAngleBox (N : ℕ) : Set (Fin N → ℝ) := Icc (fun _ => -Real.pi) (fun _ => Real.pi)

theorem angleBox_signed_translation (N : ℕ) (F : (Fin N → ℝ) → ℂ) :
    (∫ x in angleBox N, F (fun i => x i-Real.pi))=∫ x in signedAngleBox N, F x := by
  let c : Fin N → ℝ := fun _ => -Real.pi
  have hm (x : Fin N → ℝ) : x+c ∈ signedAngleBox N ↔ x∈angleBox N := by
    constructor
    · intro hx
      constructor <;> intro i
      · have h := hx.1 i; change -Real.pi ≤ x i-Real.pi at h; linarith
      · have h := hx.2 i; change x i-Real.pi ≤ Real.pi at h; linarith
    · intro hx
      constructor <;> intro i
      · have h := hx.1 i; change 0≤x i at h
        change -Real.pi ≤ x i-Real.pi; linarith
      · have h := hx.2 i; change x i≤2*Real.pi at h
        change x i-Real.pi≤Real.pi; linarith
  have hi : (fun x => (signedAngleBox N).indicator F (x+c))=
      (angleBox N).indicator (fun x => F (x+c)) := by
    funext x
    by_cases hx : x∈angleBox N
    · simp only [indicator_of_mem hx,indicator_of_mem ((hm x).mpr hx)]
    · simp only [indicator_of_notMem hx,indicator_of_notMem (fun h => hx ((hm x).mp h))]
  have he := integral_add_right_eq_self (μ := volume) ((signedAngleBox N).indicator F) c
  rw [hi] at he
  have hleft := integral_indicator (μ := volume) (f := fun x : Fin N → ℝ => F (x+c)) (s := angleBox N) measurableSet_Icc
  have hright := integral_indicator (μ := volume) (f := F) (s := signedAngleBox N) measurableSet_Icc
  have hfinal := hleft.symm.trans (he.trans hright)
  have hfun : (fun x : Fin N → ℝ => F (x+c))=(fun x => F (fun i => x i-Real.pi)) := by
    funext x
    congr 1
  rw [hfun] at hfinal
  exact hfinal

theorem angleBox_eq_signed_integral (N : ℕ) (F : (Fin N → ℝ) → ℂ)
    (hF : Continuous F) (hp : CoordinatePeriodic N F) :
    (∫ x in angleBox N,F x)=∫ x in signedAngleBox N,F x := by
  have hh := angleBox_integral_shift N F hF hp (fun _ => -Real.pi)
  simpa only [← sub_eq_add_neg] using hh.symm.trans (angleBox_signed_translation N F)

theorem angleBox_eq_signed_real_integral (N : ℕ) (F : (Fin N → ℝ) → ℝ)
    (hF : Continuous F)
    (hp : ∀ x : Fin N → ℝ, ∀ i : Fin N, F (Function.update x i (x i+2*Real.pi))=F x) :
    (∫ x in angleBox N,F x)=∫ x in signedAngleBox N,F x := by
  have hh := angleBox_eq_signed_integral N (fun x => (F x:ℂ)) (Complex.continuous_ofReal.comp hF)
    (fun x i => congrArg Complex.ofReal (hp x i))
  simpa only [integral_complex_ofReal,Complex.ofReal_inj] using hh

theorem weightedAngularJet_periodic (N : ℕ) (f : SelectorFunctions) (hf : RegularSelector f)
    (r tau lam : ℝ) (w : (Fin N → ℝ) → ℂ) (hp : CoordinatePeriodic N w) (s : ℂ) (j : ℕ) :
    CoordinatePeriodic N (fun theta => w theta*iteratedDeriv j (fun z => pulledDensity f r tau lam z theta) s) := by
  intro theta q
  have he : (fun z => pulledDensity f r tau lam z (Function.update theta q (theta q+2*Real.pi)))=
      (fun z => pulledDensity f r tau lam z theta) := by
    funext z
    exact pulledDensity_periodic N f hf r tau lam z theta q
  dsimp only
  rw [hp theta q,he]

theorem weightedAngularIntegral_signed_jets (N : ℕ) (hN : 0 < N)
    (f : SelectorFunctions) (hf : RegularSelector f) {r tau lam : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (htau : 0 ≤ tau) (hlam : 0 ≤ lam)
    (w : (Fin N → ℝ) → ℂ) (hw : Continuous w) (hp : CoordinatePeriodic N w)
    (s : ℂ) (hs : s∈dampingDomain r) (j : ℕ) :
    iteratedDeriv j (weightedAngularIntegral N f r tau lam w) s =
      ∫ theta in signedAngleBox N,w theta*iteratedDeriv j (fun z => pulledDensity f r tau lam z theta) s := by
  obtain ⟨he,hc⟩ := weightedAngularIntegral_jets N hN f hf hr hr1 htau hlam w hw s hs j
  exact he.trans (angleBox_eq_signed_integral N _ hc (weightedAngularJet_periodic N f hf r tau lam w hp s j))

theorem weightedAngularJet_norm_signed (N : ℕ) (hN : 0 < N)
    (f : SelectorFunctions) (hf : RegularSelector f) {r tau lam : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (htau : 0 ≤ tau) (hlam : 0 ≤ lam)
    (w : (Fin N → ℝ) → ℂ) (hw : Continuous w) (hp : CoordinatePeriodic N w)
    (s : ℂ) (hs : s∈dampingDomain r) (j : ℕ) :
    (∫ theta in angleBox N,‖w theta*iteratedDeriv j (fun z => pulledDensity f r tau lam z theta) s‖)=
      ∫ theta in signedAngleBox N,‖w theta*iteratedDeriv j (fun z => pulledDensity f r tau lam z theta) s‖ :=
  angleBox_eq_signed_real_integral N _
    (weightedAngularIntegral_jets N hN f hf hr hr1 htau hlam w hw s hs j).2.norm
    (fun theta i => congrArg norm (weightedAngularJet_periodic N f hf r tau lam w hp s j theta i))

theorem signed_weighted_jet_restrict {N : ℕ} (F : ℂ → (Fin N → ℝ) → ℂ)
    (w : (Fin N → ℝ) → ℂ) (S : Set (Fin N → ℝ)) (hS : S ⊆ signedAngleBox N)
    (hcover : ∀ theta∈signedAngleBox N,w theta≠0 → theta∈S) (s : ℂ) (j : ℕ) :
    (∫ theta in signedAngleBox N,w theta*iteratedDeriv j (fun z => F z theta) s)=
      ∫ theta in S,w theta*iteratedDeriv j (fun z => F z theta) s := by
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Icc hS
  intro theta htheta
  have hw : w theta=0 := by by_contra h; exact htheta.2 (hcover theta htheta.1 h)
  rw [hw,zero_mul]

end
end IsingBulk.Tail
