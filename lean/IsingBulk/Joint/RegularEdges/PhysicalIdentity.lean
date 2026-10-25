import IsingBulk.Joint.RegularEdges.PhysicalAngular
import IsingBulk.Joint.FormFactors.FiniteHolomorphy
import IsingBulk.Joint.FormFactors.HolomorphicIdentity
import IsingBulk.Joint.FormFactors.HighPunctured
import IsingBulk.Joint.Geometry.Components
import IsingBulk.Joint.Slices.ExactDomains

/-! # Actual joint contour-to-angular gluing
The real two-dimensional identity is propagated by complex Frechet
holomorphy, never by an ambient-nonextension-to-slice inference.
-/
namespace IsingBulk.Joint.RegularEdges
noncomputable section
open IsingBulk.First Set Filter Metric
open scoped Topology

theorem fullCoefficient_eq_physicalAngular_germ (n : ℕ) {x y : ℝ}
    (hx : 0<x) (hy : 0<y) (hp : Real.sinh x*Real.sinh y≠1)
    (hK : ((x:ℂ),(y:ℂ))∉spectralSet) :
    FormFactors.unscaledFullCoefficient (n+1) =ᶠ[𝓝 ((x:ℂ),(y:ℂ))]
      Negative.unscaledAngularCoefficient n := by
  let U : Set Coupling := spectralSetᶜ ∩ {K | S K≠0 ∧ 0<K.1.re ∧ 0<K.2.re ∧ p K≠1}
  have hU : IsOpen U := spectralSet_isClosed.isOpen_compl.inter
    ((isOpen_ne_fun continuous_S continuous_const).inter
      ((isOpen_lt continuous_const (Complex.continuous_re.comp continuous_fst)).inter
        ((isOpen_lt continuous_const (Complex.continuous_re.comp continuous_snd)).inter
          (isOpen_ne_fun continuous_p continuous_const))))
  have hKU : ((x:ℂ),(y:ℂ))∈U := by
    refine ⟨hK,?_,hx,hy,?_⟩
    · change Complex.sinh (x:ℂ)≠0
      rw [←Complex.ofReal_sinh]
      exact Complex.ofReal_ne_zero.mpr (Real.sinh_pos_iff.mpr hx).ne'
    · intro he
      apply hp
      have hh := congrArg Complex.re he
      simpa [p,S,T,←Complex.ofReal_sinh] using hh
  obtain ⟨r,hr,hrU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hKU)
  let V : Set Coupling := ball (x:ℂ) r ×ˢ ball (y:ℂ) r
  have hVU : V⊆U := by
    intro K hK
    apply hrU
    simpa only [V,mem_prod,mem_ball,Prod.dist_eq,max_lt_iff] using hK
  have hf : DifferentiableOn ℂ (FormFactors.unscaledFullCoefficient (n+1)) V := by
    intro K hK
    exact (FormFactors.unscaledFullCoefficient_contDiffAt 1 (n+1) (by omega)
      (hVU hK).1).differentiableAt_one.differentiableWithinAt
  have hg : DifferentiableOn ℂ (Negative.unscaledAngularCoefficient n) V := by
    intro K hK
    exact (physicalAngular_contDiffAt 1 n (hVU hK).1
      (hVU hK).2.1).differentiableAt_one.differentiableWithinAt
  have hreal (a t : ℝ) (ht : t∈Ioo (a-r/2) (a+r/2)) : (t:ℂ)∈ball (a:ℂ) r := by
    rw [mem_ball,dist_eq_norm,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,abs_lt]
    constructor <;> linarith [ht.1,ht.2]
  have heq := FormFactors.holomorphic_eqOn_product_of_real_rectangle
    isOpen_ball isOpen_ball (convex_ball _ _).isPreconnected (convex_ball _ _).isPreconnected
    hf hg (show x-r/2<x+r/2 by linarith) (show y-r/2<y+r/2 by linarith)
    (hreal x) (hreal y) (by
      intro a ha c hc
      have hL := hVU (show ((a:ℂ),(c:ℂ))∈V from ⟨hreal x a ha,hreal y c hc⟩)
      apply fullCoefficient_eq_physicalAngular_real n hL.2.2.1 hL.2.2.2.1 _ hL.1
      intro hpac
      change Real.sinh a*Real.sinh c=1 at hpac
      apply hL.2.2.2.2
      change Complex.sinh (a:ℂ)*Complex.sinh (c:ℂ)=1
      rw [←Complex.ofReal_sinh,←Complex.ofReal_sinh,←Complex.ofReal_mul,hpac,Complex.ofReal_one])
  exact Filter.mem_of_superset ((isOpen_ball.prod isOpen_ball).mem_nhds
    (show ((x:ℂ),(y:ℂ))∈V from ⟨mem_ball_self hr,mem_ball_self hr⟩)) heq

/-- Joint continuation on any actual connected open subset of the spectral
complement with nonzero first sinh, anchored at a real physical point. -/
theorem fullCoefficient_eq_physicalAngular_on_domain (n : ℕ) {D : Set Coupling}
    (hD : IsOpen D) (hDc : IsPreconnected D) (hDs : D⊆spectralSetᶜ)
    (hDS : ∀ K∈D, S K≠0) {x y : ℝ} (hx : 0<x) (hy : 0<y)
    (hp : Real.sinh x*Real.sinh y≠1) (hxy : ((x:ℂ),(y:ℂ))∈D) :
    EqOn (FormFactors.unscaledFullCoefficient (n+1)) (Negative.unscaledAngularCoefficient n) D := by
  apply FormFactors.holomorphic_eqOn_of_germ hD hDc
    (fun K hK => (FormFactors.unscaledFullCoefficient_contDiffAt 1 (n+1) (by omega)
      (hDs hK)).differentiableAt_one.differentiableWithinAt)
    (fun K hK => (physicalAngular_contDiffAt 1 n (hDs hK) (hDS K hK)).differentiableAt_one.differentiableWithinAt)
    hxy
  exact fullCoefficient_eq_physicalAngular_germ n hx hy hp (hDs hxy)


/-- Actual low-temperature joint contour coefficients equal the full angular
coefficients throughout the independently defined two-coupling domain. -/
theorem fullCoefficient_eq_physicalAngular_low (n : ℕ) :
    EqOn (FormFactors.unscaledFullCoefficient (n+1)) (Negative.unscaledAngularCoefficient n) lowDomain := by
  let x := Anisotropic.criticalPoint 1+1
  have hc : 0<Anisotropic.criticalPoint 1 := Anisotropic.criticalPoint_pos (by norm_num)
  have hx : 0<x := by dsimp [x]; linarith
  have hxc : Anisotropic.criticalPoint 1<x := by dsimp [x]; linarith
  have hp : Real.sinh x*Real.sinh x≠1 := by
    have hh := (Anisotropic.criticalPoint_lt_iff_product_gt_one (by norm_num : (0:ℝ)<1) hx.le).mp hxc
    simpa [Anisotropic.FormFactors.realProduct] using hh.ne'
  have hxy : ((x:ℂ),(x:ℂ))∈lowDomain := by
    have hh : (x:ℂ)∈ratioSlice 1 ⁻¹' lowDomain := by
      rw [lowDomain_pullback (by norm_num)]
      exact (Anisotropic.real_mem_omegaL_iff (by norm_num) x).mpr hxc
    simpa [ratioSlice] using hh
  exact fullCoefficient_eq_physicalAngular_on_domain n lowDomain_isOpen lowDomain_isPreconnected
    lowDomain_subset_spectralComplement
    (fun K hK => Anisotropic.sinh_ne_zero_of_re_pos hK.1) hx hx hp hxy


/-- The actual high-temperature joint contour/angular identity. Only the
coordinate singularity `S=0` is excluded from the angular representation. -/
theorem fullCoefficient_eq_physicalAngular_high (n : ℕ) {K : Coupling}
    (hK : K∈highDomain) (hS : S K≠0) :
    FormFactors.unscaledFullCoefficient (n+1) K=Negative.unscaledAngularCoefficient n K := by
  let x := Anisotropic.criticalPoint 1/2
  have hc : 0<Anisotropic.criticalPoint 1 := Anisotropic.criticalPoint_pos (by norm_num)
  have hx : 0<x := by dsimp [x]; positivity
  have hxc : x<Anisotropic.criticalPoint 1 := by dsimp [x]; linarith
  have hp : Real.sinh x*Real.sinh x≠1 := by
    have hh := Anisotropic.highRealRadicand_pos (by norm_num : (0:ℝ)<1) hx.le hxc
    intro he
    have hp' : Anisotropic.FormFactors.realProduct 1 x=1 := by
      simpa [Anisotropic.FormFactors.realProduct] using he
    rw [hp'] at hh
    norm_num at hh
  have hxy : ((x:ℂ),(x:ℂ))∈highDomain ∩ {L | S L≠0} := by
    constructor
    · have hh : (x:ℂ)∈ratioSlice 1 ⁻¹' highDomain := by
        rw [highDomain_pullback (by norm_num)]
        exact Anisotropic.real_mem_omegaH_of_nonneg_lt_critical (by norm_num) hx.le hxc
      simpa [ratioSlice] using hh
    · change Complex.sinh (x:ℂ)≠0
      exact Anisotropic.sinh_ne_zero_of_re_pos hx
  exact fullCoefficient_eq_physicalAngular_on_domain n FormFactors.highNonzeroDomain_isOpen
    FormFactors.highDomain_inter_S_ne_zero_isPreconnected
    (fun _ hL => highDomain_subset_spectralComplement hL.1) (fun _ hL => hL.2) hx hx hp hxy ⟨hK,hS⟩

end
end IsingBulk.Joint.RegularEdges
