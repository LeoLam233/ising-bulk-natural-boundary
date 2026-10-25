import IsingBulk.Joint.Negative.FamilyPhysicalSum
import IsingBulk.Joint.Negative.FamilySeriesLimit
import IsingBulk.Joint.Negative.FamilyFiniteJets
import IsingBulk.Joint.Negative.FamilyInteriorTails
import IsingBulk.Joint.Negative.FamilyAllJetMajorant
import IsingBulk.Joint.Negative.FamilyCurveData

/-! Uniform boundary approach of the actual complete high-temperature series.
One common inward full-resolvent tail envelope and genuinely joint finite-term
jet continuity are used before dominated passage through the infinite sum. -/
namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter Metric
open scoped Topology
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
set_option maxHeartbeats 2000000

/-- Actual full physical boundary jets converge uniformly across the compact
complex family. This is not deduced from pointwise limits: the proof uses one
summable all-particle envelope on a common inward neighborhood. -/
theorem compact_negative_high_weighted_boundary_jets {Q : Set E}
    (curve : ℂ × E→Coupling) (amp : ℂ × E→ℂ) {b : ℝ}
    (hQ : IsCompact Q) (hc : ∀eta∈Q,AnalyticAt ℂ curve (0,eta))
    (ha : ∀eta∈Q,AnalyticAt ℂ amp (0,eta))
    (hS : ∀eta∈Q,S (curve (0,eta))≠0)
    (hB : ∀eta∈Q,(transferB (curve (0,eta))).im<0)
    (hK : ∀eta∈Q,curve (0,eta)∈frontier highDomain)
    (hp : ∀eta∈Q,p (curve (0,eta))^2≠1) (hb : |b|<1)
    (he : ∀eta∈Q,∀ᶠt : ℂ in 𝓝 0,transferC (curve (t,eta))+transferB (curve (t,eta))=
      (b:ℂ)+transferB (curve (t,eta))*t)
    (hsq : ∀eta∈Q,∀ᶠt : ℂ in 𝓝 0,amp (t,eta)^2=p (curve (t,eta))) :
    ∀j : ℕ,TendstoUniformlyOn
      (fun ε : ℝ=>fun eta=>iteratedDeriv j
        (weightedPhysicalHigh (fun t=>curve (t,eta)) (fun t=>amp (t,eta))) (-(ε:ℂ)))
      (fun eta=>∑'n : ℕ,iteratedDeriv j
        (fun t=>amp (t,eta)^(2*n+1)*continuedAngularCoefficient (2*n) (curve (t,eta))) 0)
      (𝓝[>] 0) Q := by
  have hedge (eta : E) (heta : eta∈Q) :
      A (curve (0,eta))+T (curve (0,eta))=(b:ℂ)*S (curve (0,eta)) := by
    have hh := (he eta heta).self_of_nhds
    simp only [mul_zero,add_zero,transferC,transferB] at hh
    rw [←add_div] at hh
    exact (div_eq_iff (hS eta heta)).mp hh
  have hBi (eta : E) (heta : eta∈Q) : 0<(-T (curve (0,eta))/S (curve (0,eta))).im := by
    simpa only [neg_div,Complex.neg_im,transferB,neg_pos] using hB eta heta
  have hn := fun eta heta=>familyPaper_nonzero (hS eta heta) (hB eta heta) (hsq eta heta)
  obtain ⟨a,ha0,htube⟩ := compact_negative_high_tube curve hQ hc hS hB hK hp hb he
  obtain ⟨δ,hδ,htails⟩ := compact_actual_negative_interior_tails curve amp hb hQ hc ha hS
    (fun eta heta=>(hn eta heta).1) hedge hBi
  obtain ⟨Gb,_hGb,_hGb0,hboundary⟩ := compact_actual_odd_boundary_summable_majorants curve amp hb hQ hc ha hS
    (fun eta heta=>(hn eta heta).1) hedge hBi
  obtain ⟨r,hr,hidentity⟩ := compact_negative_high_weighted_jets_identity curve amp hQ hc ha hS hB hK hp hb he hsq
  intro j
  let f : ℝ→E→ℕ→ℂ := fun ε eta n=>iteratedDeriv j
    (fun t=>amp (t,eta)^(2*n+1)*continuedAngularCoefficient (2*n) (curve (t,eta))) (-(ε:ℂ))
  let g : E→ℕ→ℂ := fun eta n=>iteratedDeriv j
    (fun t=>amp (t,eta)^(2*n+1)*continuedAngularCoefficient (2*n) (curve (t,eta))) 0
  obtain ⟨G,hG,_hG0,hbound⟩ := htails j
  have hH : Summable (fun k : ℕ=>G (2*k+1)) :=
    hG.comp_injective (i:=fun k : ℕ=>2*k+1) (by intro k l h; dsimp at h; omega)
  have htail : ∀ᶠε : ℝ in 𝓝[>] 0,∀eta∈Q,∀k,‖f ε eta (k+(j+2))‖≤G (2*k+1) := by
    filter_upwards [Ioo_mem_nhdsGT (lt_min ha0 hδ)] with ε hε eta heta k
    have hnorm : ‖-(ε:ℂ)‖=ε := by simp only [norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hε.1]
    have hd := htube eta heta (-(ε:ℂ)) (by rw [hnorm]; exact hε.2.trans_le (min_le_left _ _))
    have hi : 0<(transferC (curve (-(ε:ℂ),eta))+transferB (curve (-(ε:ℂ),eta))-(b:ℂ)).im := by
      rw [hd.2.2.2.1,add_sub_cancel_left]
      simpa only [Complex.mul_im,Complex.neg_re,Complex.ofReal_re,Complex.neg_im,Complex.ofReal_im,
        neg_zero,mul_zero,zero_add] using mul_pos_of_neg_of_neg hd.2.2.1 (neg_neg_of_pos hε.1)
    have hh := hbound eta heta (-(ε:ℂ)) (by rw [hnorm]; exact hε.2.trans_le (min_le_right _ _)) hi (2*k+1)
    simpa only [f,show 2*j+3+(2*k+1)=2*(k+(j+2)) by omega] using hh
  have hlim (n : ℕ) : TendstoUniformlyOn (fun ε eta=>f ε eta n) (fun eta=>g eta n) (𝓝[>] 0) Q :=
    compact_family_weighted_negative_jet_limit (2*n) j ⟨n,by omega⟩ curve amp hQ hc ha hS hedge hb hBi
  have hs := uniform_tsum_of_common_tail f g Q (j+2) (Gb j) (fun k=>G (2*k+1)) hH
    (fun eta heta n=>hboundary eta heta j n) htail hlim
  rw [Metric.tendstoUniformlyOn_iff] at hs ⊢
  intro ε hε
  filter_upwards [hs ε hε,Ioo_mem_nhdsGT hr] with t ht htr eta heta
  have heq := (hidentity eta heta t htr.1 htr.2 j).tsum_eq
  change dist (∑'n,g eta n) _<ε
  rw [←heq]
  exact ht eta heta

end
end IsingBulk.Joint.Negative
