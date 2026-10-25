import IsingBulk.Joint.Negative.FamilyCurveData
import IsingBulk.Joint.Negative.FamilyAllJetMajorant
import IsingBulk.Joint.Negative.FamilyOuterCauchy
import IsingBulk.Joint.Negative.FamilyNonresonantCauchy

/-! All actual complete coefficient ranges on one compact complex family.
Only actual analytic curve, physical amplitude and edge chart data are inputs.
Every growing-dimensional normal form, winding sum, contour transport and
particle estimate is constructed by the proof. -/
namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter MeasureTheory IsingBulk.Anisotropic
open IsingBulk.Anisotropic.NegativeDominance IsingBulk.Anisotropic.RegularEdges
open IsingBulk.Anisotropic.NegativeCycles
open scoped Topology BigOperators
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
set_option maxHeartbeats 2000000

theorem compact_normalized_negative_family_ranges
    {Q : Set E} (curve : ℂ × E→Coupling) (amp : ℂ × E→ℂ)
    (hQ : IsCompact Q) (hc : ∀eta∈Q,AnalyticAt ℂ curve (0,eta))
    (ha : ∀eta∈Q,AnalyticAt ℂ amp (0,eta))
    (hS : ∀eta∈Q,S (curve (0,eta))≠0)
    (hB : ∀eta∈Q,(transferB (curve (0,eta))).im<0)
    (phi : ℝ) (hphi0 : 0<phi) (hphipi : phi<Real.pi) (hphi : Real.sin phi≠0)
    (he : ∀eta∈Q,∀ᶠt : ℂ in 𝓝 0,transferC (curve (t,eta))+transferB (curve (t,eta))=
      (Real.cos phi:ℂ)+transferB (curve (t,eta))*t)
    (hsq : ∀eta∈Q,∀ᶠt : ℂ in 𝓝 0,amp (t,eta)^2=p (curve (t,eta)))
    (p0 : ℕ) (hp : 2≤p0) (hpo : Odd p0)
    (hphase : IsPrimitiveRoot (IsingBulk.Tail.continuedRoot (Real.cos phi:ℂ)) p0)
    (hres : ∀m : ℕ,p0∣2*m+1 → Complex.exp (((2*m+1:ℕ):ℂ)*((phi:ℂ)*Complex.I))=1) :
    ∃a E0 D C : ℝ,0<a ∧ 0<E0 ∧ 0<D ∧ ∀ᶠj : ℕ in atTop,∀eta∈Q,
      HasCoefficientRanges (negativePaperCoefficient (fun t=>curve (t,eta)) (familyMember amp eta))
        (familyMember (familyPaperB curve) eta) (familyMember (familyPaperRoot curve amp) eta)
        phi p0 a D C (actualMiddleErrorScale E0) j := by
  have hb : |Real.cos phi|<1 := (sq_lt_one_iff_abs_lt_one _).mp (by
    nlinarith [Real.sin_sq_add_cos_sq phi,sq_pos_of_ne_zero hphi])
  have hn := fun eta heta=>familyPaper_nonzero (hS eta heta) (hB eta heta) (hsq eta heta)
  have hca (eta : E) (heta : eta∈Q) : AnalyticAt ℂ (fun t=>curve (t,eta)) 0 :=
    (hc eta heta).comp (f:=fun t : ℂ=>(t,eta)) (analyticAt_id.prod analyticAt_const)
  have haa (eta : E) (heta : eta∈Q) : AnalyticAt ℂ (familyMember amp eta) 0 :=
    familyMember_analyticAt (ha eta heta)
  have hedge (eta : E) (heta : eta∈Q) :
      A (curve (0,eta))+T (curve (0,eta))=(Real.cos phi:ℂ)*S (curve (0,eta)) := by
    have hh := (he eta heta).self_of_nhds
    simp only [mul_zero,add_zero,transferC,transferB] at hh
    rw [←add_div] at hh
    exact (div_eq_iff (hS eta heta)).mp hh
  have hBi (eta : E) (heta : eta∈Q) : 0<(-T (curve (0,eta))/S (curve (0,eta))).im := by
    simpa only [neg_div,Complex.neg_im,transferB,neg_pos] using hB eta heta
  have hchart (eta : E) (heta : eta∈Q) : ∀ᶠt : ℂ in 𝓝 0,S (curve (t,eta))≠0 ∧
      familyPaperB curve (t,eta)=T (curve (t,eta))/S (curve (t,eta)) ∧
      transferC (curve (t,eta))+transferB (curve (t,eta))=
        (Real.cos phi:ℂ)+familyPaperB curve (t,eta)*t ∧
      familyMember amp eta t^2=p (curve (t,eta)) ∧
      familyMember amp eta t/S (curve (t,eta))=familyPaperRoot curve amp (t,eta) := by
    have hsa : AnalyticAt ℂ (fun t=>S (curve (t,eta))) 0 :=
      Complex.analyticAt_sinh.comp (analyticAt_fst.comp (hca eta heta))
    filter_upwards [hsa.continuousAt.eventually_ne (hS eta heta),he eta heta,hsq eta heta] with t hst het hqt
    exact ⟨hst,rfl,het,hqt,rfl⟩
  obtain ⟨a,Dlow,haR,hDlow,hlow⟩ := compact_actual_odd_normalized_cauchy curve amp hb hQ hc ha hS
    (fun eta heta=>(hn eta heta).1) hedge hBi
  obtain ⟨aR,CR,haRR,_hCR,hnonres⟩ := compact_actual_nonresonant_gaussian curve amp hb hQ hc ha hS
    (fun eta heta=>(hn eta heta).1) hedge hBi hp hphase
  have houter := fun s hs=>compact_actual_outer_gaussian curve amp hb hQ hc ha hS
    (fun eta heta=>(hn eta heta).1) hedge hBi s hs
  obtain ⟨E0,D,C,hE,hD,hranges⟩ := compact_family_negative_paper_ranges
    (familyPaperB curve) (familyPaperRoot curve amp) phi hphi hphi0 hphipi hQ
    (fun eta heta=>familyPaperB_analyticAt (hc eta heta) (hS eta heta))
    (fun eta heta=>(hn eta heta).2.1)
    (fun eta heta=>familyPaperRoot_analyticAt (hc eta heta) (ha eta heta) (hS eta heta))
    (fun eta heta=>(hn eta heta).2.2)
    (fun eta heta=>familyPaper_square_germ (hc eta heta) (hS eta heta) (hsq eta heta))
    (fun eta t=>curve (t,eta)) (familyMember amp) hca haa hS hedge hb hBi hchart houter
    p0 (by omega) hpo hres a Dlow aR CR haR hDlow.le haRR hlow
    (fun eta heta j m hm=>hnonres eta heta m j hm)
  exact ⟨a,E0,D,C,haR,hE,hD,hranges⟩

end
end IsingBulk.Joint.Negative
