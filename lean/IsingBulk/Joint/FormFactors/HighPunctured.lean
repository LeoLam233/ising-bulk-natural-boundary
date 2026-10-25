import IsingBulk.Joint.Geometry.HighTopology
import IsingBulk.Joint.Isotropic.Geometry
import Mathlib.Analysis.Complex.Convex

/-! Connectedness needed for identifying physical angular and double-contour
coefficients. The puncture is the actual coordinate hyperplane, not a ray. -/
namespace IsingBulk.Joint.FormFactors
noncomputable section
open Set Metric
open scoped Topology

def highNonzeroDomain : Set Coupling := {K | K ∈ highDomain ∧ S K ≠ 0}

theorem S_eq_zero_iff_fst_eq_zero {K : Coupling} (hK : K ∈ highDomain) :
    S K = 0 ↔ K.1 = 0 := by
  constructor
  · intro hs
    apply sinh_injOn_central hK.1 (show |(0:ℂ).im| < Real.pi/2 by simp; positivity)
    simpa only [S,Complex.sinh_zero] using hs
  · intro h; simp [S,h]

theorem highDomain_scale_second {K : Coupling} (hK : K ∈ highDomain)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) : (K.1,t • K.2) ∈ highDomain := by
  rcases hK with ⟨hy,hv,h₁,h₂⟩
  have habs (v : ℝ) : |t*v| ≤ |v| := by
    rw [abs_mul,abs_of_nonneg ht]
    exact mul_le_of_le_one_left (abs_nonneg v) ht1
  have hv' : |t*K.2.im| < Real.pi/2 := (habs _).trans_lt hv
  have htanh := Anisotropic.tanh_strictMono.monotone (habs K.2.re)
  have hfirst := (mul_le_mul_of_nonneg_left htanh (Real.cosh_pos K.1.re).le).trans_lt h₁
  have hc : Real.cosh (t*K.2.re) ≤ Real.cosh K.2.re := Real.cosh_le_cosh.mpr (habs _)
  have hn : 0 ≤ Real.tanh |K.1.re| := by
    simpa using Anisotropic.tanh_strictMono.monotone (abs_nonneg K.1.re)
  have hsecond := (mul_le_mul_of_nonneg_right hc hn).trans_lt h₂
  have hcos := Anisotropic.cos_scale_ge (y := K.2.im) (by linarith [Real.pi_pos]) ht ht1
  exact ⟨hy,by simpa only [Complex.smul_im,smul_eq_mul] using hv',
    by simpa only [Complex.smul_re,smul_eq_mul] using hfirst,
    by simpa only [Complex.smul_re,Complex.smul_im,smul_eq_mul] using hsecond.trans_le hcos⟩

theorem axis_mem_highDomain {z : ℂ} (hz : |z.im| < Real.pi/2) : (z,0) ∈ highDomain := by
  refine ⟨hz,?_,?_,?_⟩
  · simp only [Complex.zero_im,abs_zero]; positivity
  · simpa only [Complex.zero_re,abs_zero,Real.tanh_zero,mul_zero] using
      Real.cos_pos_of_mem_Ioo (abs_lt.mp hz)
  · simpa only [Complex.zero_re,Complex.zero_im,Real.cosh_zero,Real.cos_zero,one_mul] using
      Real.tanh_lt_one |z.re|

theorem punctured_central_strip_preconnected :
    IsPreconnected {z : ℂ | |z.im| < Real.pi/2 ∧ z ≠ 0} := by
  let A : Set ℂ := {z | 0 < z.im ∧ z.im < Real.pi/2}
  let B : Set ℂ := {z | 0 < z.re ∧ -(Real.pi/2) < z.im ∧ z.im < Real.pi/2}
  let C : Set ℂ := {z | -(Real.pi/2) < z.im ∧ z.im < 0}
  let D : Set ℂ := {z | z.re < 0 ∧ -(Real.pi/2) < z.im ∧ z.im < Real.pi/2}
  have hA : IsPreconnected A := ((convex_halfSpace_im_gt 0).inter (convex_halfSpace_im_lt _)).isPreconnected
  have hB : IsPreconnected B := ((convex_halfSpace_re_gt 0).inter
    ((convex_halfSpace_im_gt _).inter (convex_halfSpace_im_lt _))).isPreconnected
  have hC : IsPreconnected C := ((convex_halfSpace_im_gt _).inter (convex_halfSpace_im_lt 0)).isPreconnected
  have hD : IsPreconnected D := ((convex_halfSpace_re_lt 0).inter
    ((convex_halfSpace_im_gt _).inter (convex_halfSpace_im_lt _))).isPreconnected
  have hAB : (A ∩ B).Nonempty := by
    refine ⟨1+((Real.pi/4:ℝ):ℂ)*Complex.I,?_⟩
    simp only [A,B,mem_inter_iff,mem_ofPred_eq]
    norm_num
    constructor
    · exact ⟨by positivity,by linarith [Real.pi_pos]⟩
    · constructor <;> linarith [Real.pi_pos]
  have hBC : ((A ∪ B) ∩ C).Nonempty := by
    refine ⟨1-((Real.pi/4:ℝ):ℂ)*Complex.I,Or.inr ?_,?_⟩
    · dsimp [B]; norm_num; constructor <;> linarith [Real.pi_pos]
    · dsimp [C]; norm_num; constructor <;> linarith [Real.pi_pos]
  have hCD : (((A ∪ B) ∪ C) ∩ D).Nonempty := by
    refine ⟨-1-((Real.pi/4:ℝ):ℂ)*Complex.I,Or.inr ?_,?_⟩
    · dsimp [C]; norm_num; constructor <;> linarith [Real.pi_pos]
    · dsimp [D]; norm_num; constructor <;> linarith [Real.pi_pos]
  have he : ((A ∪ B) ∪ C) ∪ D = {z : ℂ | |z.im| < Real.pi/2 ∧ z ≠ 0} := by
    ext z
    simp only [A,B,C,D,mem_union,mem_ofPred_eq,abs_lt]
    constructor
    · rintro (((hz | hz) | hz) | hz)
      · refine ⟨⟨by linarith [Real.pi_pos],hz.2⟩,?_⟩
        intro he; subst z; simpa using hz.1
      · exact ⟨hz.2,fun he => by subst z; simpa using hz.1⟩
      · refine ⟨⟨hz.1,by linarith [Real.pi_pos]⟩,?_⟩
        intro he; subst z; simpa using hz.2
      · exact ⟨hz.2,fun he => by subst z; simpa using hz.1⟩
    · rintro ⟨hz,hne⟩
      rcases lt_trichotomy 0 z.im with hi | hi | hi
      · exact Or.inl (Or.inl (Or.inl ⟨hi,hz.2⟩))
      · have hr : z.re ≠ 0 := fun hr => hne (Complex.ext hr hi.symm)
        rcases lt_or_gt_of_ne hr with hr | hr
        · exact Or.inr ⟨hr,hz⟩
        · exact Or.inl (Or.inl (Or.inr ⟨hr,hz⟩))
      · exact Or.inl (Or.inr ⟨hz.1,hi⟩)
  rw [← he]
  obtain ⟨a,haA,haB⟩ := hAB
  obtain ⟨b,hbAB,hbC⟩ := hBC
  obtain ⟨c,hcABC,hcD⟩ := hCD
  exact IsPreconnected.union c hcABC hcD
    (IsPreconnected.union b hbAB hbC (IsPreconnected.union a haA haB hA hB) hC) hD


theorem highNonzeroDomain_isOpen : IsOpen highNonzeroDomain :=
  highDomain_isOpen.inter (isOpen_ne_fun continuous_S continuous_const)

theorem highNonzeroDomain_isPreconnected : IsPreconnected highNonzeroDomain := by
  let Z : Set Coupling := (fun z : ℂ => (z,0)) '' {z : ℂ | |z.im| < Real.pi/2 ∧ z ≠ 0}
  have hZ : IsPreconnected Z := punctured_central_strip_preconnected.image _
    (continuous_id.prodMk continuous_const).continuousOn
  have hZU : Z ⊆ highNonzeroDomain := by
    rintro K ⟨z,hz,rfl⟩
    have hK := axis_mem_highDomain hz.1
    exact ⟨hK,fun he => hz.2 ((S_eq_zero_iff_fst_eq_zero hK).mp he)⟩
  have hbase {K : Coupling} (hK : K ∈ highNonzeroDomain) : (K.1,0) ∈ Z :=
    ⟨K.1,⟨hK.1.1,fun he => hK.2 ((S_eq_zero_iff_fst_eq_zero hK.1).mpr he)⟩,rfl⟩
  have hseg {K : Coupling} (hK : K ∈ highNonzeroDomain) :
      segment ℝ (K.1,0) K ⊆ highNonzeroDomain := by
    rintro L ⟨a,b,ha,hb,hab,rfl⟩
    have hb1 : b ≤ 1 := by linarith
    have he : a • (K.1,0) + b • K = (K.1,b • K.2) := by
      apply Prod.ext
      · change a • K.1+b • K.1=K.1
        rw [← add_smul,hab,one_smul]
      · simp only [Prod.snd_add,Prod.smul_snd,smul_zero,zero_add]
    rw [he]
    exact ⟨highDomain_scale_second hK.1 hb hb1,hK.2⟩
  apply isPreconnected_of_forall_pair
  intro K hK L hL
  let Q := (Z ∪ segment ℝ (K.1,0) K) ∪ segment ℝ (L.1,0) L
  refine ⟨Q,?_,Or.inl (Or.inr (right_mem_segment ℝ _ _)),
    Or.inr (right_mem_segment ℝ _ _),?_⟩
  · exact union_subset (union_subset hZU (hseg hK)) (hseg hL)
  · exact IsPreconnected.union (L.1,0) (Or.inl (hbase hL)) (left_mem_segment ℝ _ _)
      (IsPreconnected.union (K.1,0) (hbase hK) (left_mem_segment ℝ _ _) hZ
        (convex_segment _ _).isPreconnected) (convex_segment _ _).isPreconnected

/-- Literal intersection form used by the physical angular bridge. -/
theorem highDomain_inter_S_ne_zero_isPreconnected :
    IsPreconnected (highDomain ∩ {K | S K ≠ 0}) := highNonzeroDomain_isPreconnected

end
end IsingBulk.Joint.FormFactors
