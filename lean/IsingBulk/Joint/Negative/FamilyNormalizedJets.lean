import IsingBulk.Joint.Negative.FamilyPhysicalJets
import IsingBulk.Joint.Negative.FamilyUniformProducts
import IsingBulk.Joint.Negative.FamilyJetLimit
import IsingBulk.Joint.Negative.FamilyDensityScalar
import IsingBulk.Joint.RegularEdges.BoundaryPrefactors
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter Metric IsingBulk.First
open scoped Topology BigOperators
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
set_option maxHeartbeats 2000000

def highBoundaryUnit (curve : ℂ × E→Coupling) (amp : ℂ × E→ℂ) (q : ℂ × E) : ℂ :=
  FormFactors.highPrefactor (curve q)/amp q

/-- The literal normalized boundary jet is the finite Leibniz convolution of
the actual physical analytic unit with the complete odd boundary jet series. -/
def normalizedHighBoundaryJet (curve : ℂ × E→Coupling) (amp : ℂ × E→ℂ) (j : ℕ) (eta : E) : ℂ :=
  ∑i∈Finset.range (j+1),(j.choose i:ℂ)*iteratedDeriv i (fun t=>highBoundaryUnit curve amp (t,eta)) 0*
    (∑'n : ℕ,iteratedDeriv (j-i)
      (fun t=>amp (t,eta)^(2*n+1)*continuedAngularCoefficient (2*n) (curve (t,eta))) 0)

theorem highBoundaryUnit_analyticAt {curve : ℂ × E→Coupling} {amp : ℂ × E→ℂ} {eta : E}
    (hc : AnalyticAt ℂ curve (0,eta)) (ha : AnalyticAt ℂ amp (0,eta)) (han : amp (0,eta)≠0)
    (hK : curve (0,eta)∈frontier highDomain) (hp : p (curve (0,eta))^2≠1) :
    AnalyticAt ℂ (highBoundaryUnit curve amp) (0,eta) :=
  ((RegularEdges.highPrefactor_boundary_analyticAt hK.1 hp).comp hc).div ha han

/-- Uniform boundary limits of every derivative of the literal normalized
high susceptibility. All unit-jet bounds and full-series bounds are derived
from the actual joint family; none is an additional premise. -/
theorem compact_negative_high_normalized_boundary_jets {Q : Set E}
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
      (fun ε : ℝ=>fun eta=>iteratedDeriv j (fun t=>FormFactors.highNormalizedBulk (curve (t,eta))) (-(ε:ℂ)))
      (normalizedHighBoundaryJet curve amp j) (𝓝[>] 0) Q := by
  have han (eta : E) (heta : eta∈Q) : amp (0,eta)≠0 :=
    (familyPaper_nonzero (hS eta heta) (hB eta heta) (hsq eta heta)).1
  have hunit (eta : E) (heta : eta∈Q) : AnalyticAt ℂ (highBoundaryUnit curve amp) (0,eta) :=
    highBoundaryUnit_analyticAt (hc eta heta) (ha eta heta) (han eta heta) (hK eta heta) (hp eta heta)
  have hedge (eta : E) (heta : eta∈Q) : A (curve (0,eta))+T (curve (0,eta))=(b:ℂ)*S (curve (0,eta)) := by
    have hh := (he eta heta).self_of_nhds
    simp only [mul_zero,add_zero,transferC,transferB] at hh
    rw [←add_div] at hh
    exact (div_eq_iff (hS eta heta)).mp hh
  have hBi (eta : E) (heta : eta∈Q) : 0<(-T (curve (0,eta))/S (curve (0,eta))).im := by
    simpa only [neg_div,Complex.neg_im,transferB,neg_pos] using hB eta heta
  obtain ⟨G,hG,hG0,hGb⟩ := compact_actual_odd_boundary_summable_majorants curve amp hb hQ hc ha hS han hedge hBi
  have hweighted := compact_negative_high_weighted_boundary_jets curve amp hQ hc ha hS hB hK hp hb he hsq
  obtain ⟨r,hr,hphys⟩ := compact_negative_high_real_approach curve hQ hc hS hB hK hp hb he
  obtain ⟨a,ha0,hamp⟩ := compact_family_parameter_nonzero amp hQ ha han
  obtain ⟨d,M,hd,_hM,hu⟩ := compact_analytic_uniform_bound (highBoundaryUnit curve amp) hQ hunit
  intro j
  let W : E→ℂ→ℂ := fun eta=>weightedPhysicalHigh (fun t=>curve (t,eta)) (fun t=>amp (t,eta))
  let V : ℕ→E→ℂ := fun k eta=>∑'n : ℕ,iteratedDeriv k
    (fun t=>amp (t,eta)^(2*n+1)*continuedAngularCoefficient (2*n) (curve (t,eta))) 0
  let f : ℕ→ℝ→E→ℂ := fun i ε eta=>(j.choose i:ℂ)*
    iteratedDeriv i (fun t=>highBoundaryUnit curve amp (t,eta)) (-(ε:ℂ))*iteratedDeriv (j-i) (W eta) (-(ε:ℂ))
  let f₀ : ℕ→E→ℂ := fun i eta=>(j.choose i:ℂ)*
    iteratedDeriv i (fun t=>highBoundaryUnit curve amp (t,eta)) 0*V (j-i) eta
  have hlim (i : ℕ) (_hi : i∈Finset.range (j+1)) : TendstoUniformlyOn (f i) (f₀ i) (𝓝[>] 0) Q := by
    have huli := compact_analytic_negative_real_jet_limit (highBoundaryUnit curve amp) hQ hunit i
    obtain ⟨c,C,hc0,hC,hbound⟩ := compact_parameter_jet_uniform_bound (highBoundaryUnit curve amp) hQ hunit i
    have hfb : ∀ᶠε : ℝ in 𝓝[>] 0,∀eta∈Q,
        ‖iteratedDeriv i (fun t=>highBoundaryUnit curve amp (t,eta)) (-(ε:ℂ))‖≤C := by
      filter_upwards [Ioo_mem_nhdsGT hc0] with ε hε eta heta
      exact (hbound eta heta (-(ε:ℂ)) (by simpa [abs_of_pos hε.1] using hε.2)).2.le
    have hgb (eta : E) (heta : eta∈Q) : ‖V (j-i) eta‖≤∑'n,G (j-i) n := by
      have hnorm := (hG (j-i)).of_nonneg_of_le (fun _=>norm_nonneg _) (hGb eta heta (j-i))
      exact (norm_tsum_le_tsum_norm hnorm).trans (Summable.tsum_le_tsum (hGb eta heta (j-i)) hnorm (hG (j-i)))
    have hm := uniform_product_of_common_bounds huli (hweighted (j-i)) hC.le
      (tsum_nonneg (hG0 (j-i))) hfb hgb
    simpa only [f,f₀,W,V,mul_assoc] using uniform_const_mul hm (j.choose i:ℂ)
  have hsum := uniform_finset_sum (Finset.range (j+1)) f f₀ hlim
  have hid : ∀ᶠε : ℝ in 𝓝[>] 0,∀eta∈Q,
      iteratedDeriv j (fun t=>FormFactors.highNormalizedBulk (curve (t,eta))) (-(ε:ℂ))=
        ∑i∈Finset.range (j+1),f i ε eta := by
    filter_upwards [Ioo_mem_nhdsGT (lt_min hr (lt_min ha0 hd))] with ε hε eta heta
    let x : ℂ := -(ε:ℂ)
    have hxn : ‖x‖=ε := by simp only [x,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hε.1]
    obtain ⟨hcx,_hSx,hdom⟩ := hphys eta heta ε hε.1 (hε.2.trans_le (min_le_left _ _))
    have hax := hamp eta heta x (by rw [hxn]; exact hε.2.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
    have hux := (hu eta heta x (by rw [hxn]; exact hε.2.trans_le ((min_le_right _ _).trans (min_le_right _ _)))).1
    have hca : AnalyticAt ℂ (fun t : ℂ=>curve (t,eta)) x :=
      hcx.comp (f:=fun t : ℂ=>(t,eta)) (analyticAt_id.prod analyticAt_const)
    have haa : AnalyticAt ℂ (fun t : ℂ=>amp (t,eta)) x :=
      hax.1.comp (f:=fun t : ℂ=>(t,eta)) (analyticAt_id.prod analyticAt_const)
    have hua : AnalyticAt ℂ (fun t : ℂ=>highBoundaryUnit curve amp (t,eta)) x :=
      hux.comp (f:=fun t : ℂ=>(t,eta)) (analyticAt_id.prod analyticAt_const)
    have hW : ContDiffAt ℂ j (W eta) x := haa.contDiffAt.mul
      ((FormFactors.high_particleSeries_contDiffAt j (highDomain_subset_spectralComplement hdom)).comp x hca.contDiffAt)
    have heq : (fun t=>FormFactors.highNormalizedBulk (curve (t,eta))) =ᶠ[𝓝 x]
        (fun t=>highBoundaryUnit curve amp (t,eta)*W eta t) := by
      filter_upwards [haa.continuousAt.eventually_ne hax.2] with t ht
      dsimp only [highBoundaryUnit,W]
      rw [weightedPhysicalHigh_eq_normalized]
      dsimp only
      field_simp [ht,FormFactors.highPrefactor_ne_zero]
    rw [heq.iteratedDeriv_eq j,iteratedDeriv_fun_mul hua.contDiffAt hW]
  rw [Metric.tendstoUniformlyOn_iff] at hsum ⊢
  intro ε hε
  filter_upwards [hsum ε hε,hid] with t ht heq eta heta
  rw [heq eta heta]
  exact ht eta heta

end
end IsingBulk.Joint.Negative
