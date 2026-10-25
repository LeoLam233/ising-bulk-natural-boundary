import IsingBulk.Joint.FormFactors.HolomorphicIdentity
import IsingBulk.Joint.FormFactors.NormalConvergence
import IsingBulk.Joint.PhysicalField.Identification
import IsingBulk.Joint.Geometry.PhysicalRegion
import Mathlib.Analysis.Calculus.FDeriv.Star

/-! Schwarz reflection for the actual independent-coupling bulk sums. Only
one common real physical spin family is used, exactly as in the baseline;
no complex continuation or reflected-identity premise is imported. -/
namespace IsingBulk.Joint.FormFactors
noncomputable section
open Set Filter Metric
open scoped Topology

@[simp] theorem star_mem_highDomain_iff (K : Coupling) : star K∈highDomain ↔ K∈highDomain := by
  rcases K with ⟨z,w⟩
  simp [highDomain,Real.cos_neg]

@[simp] theorem star_mem_lowDomain_iff (K : Coupling) : star K∈lowDomain ↔ K∈lowDomain := by
  rcases K with ⟨z,w⟩
  simp [lowDomain,Real.cos_neg]

/-- A positive real two-dimensional physical germ determines a reflected
holomorphic function on the connected open joint domain. -/
theorem reflection_eqOn_of_real_physical_point {D : Set Coupling}
    (hD : IsOpen D) (hDc : IsPreconnected D)
    (hstar : ∀ K, star K∈D ↔ K∈D) {f : Coupling → ℂ}
    (hf : DifferentiableOn ℂ f D)
    (hreal : ∀ a c : ℝ, 0<a → 0<c → ((a:ℂ),(c:ℂ))∈D →
      star (f ((a:ℂ),(c:ℂ)))=f ((a:ℂ),(c:ℂ)))
    {x y : ℝ} (hx : 0<x) (hy : 0<y) (hxy : ((x:ℂ),(y:ℂ))∈D) :
    EqOn (fun K => star (f (star K))) f D := by
  have hg : DifferentiableOn ℂ (fun K => star (f (star K))) D := by
    intro K hK
    have hh := ((hf (star K) ((hstar K).mpr hK)).differentiableAt
      (hD.mem_nhds ((hstar K).mpr hK))).star_star
    simpa only [Function.comp_def,star_star] using hh.differentiableWithinAt (s := D)
  apply holomorphic_eqOn_of_germ hD hDc hg hf hxy
  let U : Set Coupling := D ∩ {K | 0<K.1.re ∧ 0<K.2.re}
  have hU : IsOpen U := hD.inter ((isOpen_lt continuous_const
    (Complex.continuous_re.comp continuous_fst)).inter
      (isOpen_lt continuous_const (Complex.continuous_re.comp continuous_snd)))
  have hKU : ((x:ℂ),(y:ℂ))∈U := ⟨hxy,hx,hy⟩
  obtain ⟨r,hr,hrU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hKU)
  let V : Set Coupling := ball (x:ℂ) r ×ˢ ball (y:ℂ) r
  have hVU : V⊆U := by
    intro K hK
    apply hrU
    simpa only [V,mem_prod,mem_ball,Prod.dist_eq,max_lt_iff] using hK
  have hrealball (a t : ℝ) (ht : t∈Ioo (a-r/2) (a+r/2)) : (t:ℂ)∈ball (a:ℂ) r := by
    rw [mem_ball,dist_eq_norm,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,abs_lt]
    constructor <;> linarith [ht.1,ht.2]
  have heq := holomorphic_eqOn_product_of_real_rectangle
    isOpen_ball isOpen_ball (convex_ball _ _).isPreconnected (convex_ball _ _).isPreconnected
    (hg.mono (fun _ hK => (hVU hK).1)) (hf.mono (fun _ hK => (hVU hK).1))
    (show x-r/2<x+r/2 by linarith) (show y-r/2<y+r/2 by linarith)
    (hrealball x) (hrealball y) (by
      intro a ha c hc
      have hL := hVU (show ((a:ℂ),(c:ℂ))∈V from ⟨hrealball x a ha,hrealball y c hc⟩)
      change star (f (star (a:ℂ),star (c:ℂ)))=f ((a:ℂ),(c:ℂ))
      simpa using hreal a c hL.2.1 hL.2.2 hL.1)
  exact Filter.mem_of_superset ((isOpen_ball.prod isOpen_ball).mem_nhds
    (show ((x:ℂ),(y:ℂ))∈V from ⟨mem_ball_self hr,mem_ball_self hr⟩)) heq

variable {corrH corrL : PhysicalField.CorrelationFamily}

theorem highNormalizedBulk_reflection
    (hphys : PhysicalField.PublishedRealSpinFamily corrH corrL) :
    EqOn (fun K => star (highNormalizedBulk (star K))) highNormalizedBulk highDomain := by
  let x := Anisotropic.criticalPoint 1/2
  have hc : 0<Anisotropic.criticalPoint 1 := Anisotropic.criticalPoint_pos (by norm_num)
  have hx : 0<x := by dsimp [x]; positivity
  have hxc : x<Anisotropic.criticalPoint 1 := by dsimp [x]; linarith
  have hxy : ((x:ℂ),(x:ℂ))∈highDomain := by
    have hh : (x:ℂ)∈ratioSlice 1 ⁻¹' highDomain := by
      rw [highDomain_pullback (by norm_num)]
      exact Anisotropic.real_mem_omegaH_of_nonneg_lt_critical (by norm_num) hx.le hxc
    simpa [ratioSlice] using hh
  apply reflection_eqOn_of_real_physical_point highDomain_isOpen highDomain_isPreconnected
    star_mem_highDomain_iff highNormalizedBulk_differentiableOn _ hx hx hxy
  intro a c ha hc hK
  have he := (PhysicalField.high_physical_identification hphys ha hc
    ((realPositive_mem_high_iff ha hc).mp hK)).2
  change highNormalizedBulk ((a:ℂ),(c:ℂ))=_ at he
  rw [he]
  simp

theorem lowNormalizedBulk_reflection
    (hphys : PhysicalField.PublishedRealSpinFamily corrH corrL) :
    EqOn (fun K => star (lowNormalizedBulk (star K))) lowNormalizedBulk lowDomain := by
  let x := Anisotropic.criticalPoint 1+1
  have hc : 0<Anisotropic.criticalPoint 1 := Anisotropic.criticalPoint_pos (by norm_num)
  have hx : 0<x := by dsimp [x]; linarith
  have hxc : Anisotropic.criticalPoint 1<x := by dsimp [x]; linarith
  have hxy : ((x:ℂ),(x:ℂ))∈lowDomain := by
    have hh : (x:ℂ)∈ratioSlice 1 ⁻¹' lowDomain := by
      rw [lowDomain_pullback (by norm_num)]
      exact (Anisotropic.real_mem_omegaL_iff (by norm_num) x).mpr hxc
    simpa [ratioSlice] using hh
  apply reflection_eqOn_of_real_physical_point lowDomain_isOpen lowDomain_isPreconnected
    star_mem_lowDomain_iff lowNormalizedBulk_differentiableOn _ hx hx hxy
  intro a c ha hc hK
  have he := (PhysicalField.low_physical_identification hphys ha hc
    ((realPositive_mem_low_iff ha hc).mp hK)).2
  change lowNormalizedBulk ((a:ℂ),(c:ℂ))=_ at he
  rw [he]
  simp

theorem highNormalizedBulk_conjugate
    (hphys : PhysicalField.PublishedRealSpinFamily corrH corrL)
    {K : Coupling} (hK : K∈highDomain) :
    highNormalizedBulk (star K)=star (highNormalizedBulk K) := by
  simpa using congrArg star (highNormalizedBulk_reflection hphys hK)

theorem lowNormalizedBulk_conjugate
    (hphys : PhysicalField.PublishedRealSpinFamily corrH corrL)
    {K : Coupling} (hK : K∈lowDomain) :
    lowNormalizedBulk (star K)=star (lowNormalizedBulk K) := by
  simpa using congrArg star (lowNormalizedBulk_reflection hphys hK)

end
end IsingBulk.Joint.FormFactors
