import IsingBulk.Joint.Geometry.RegularFace
import IsingBulk.Joint.Geometry.PhysicalRegion

namespace IsingBulk.Joint
noncomputable section
open Set Filter
open scoped Topology

def realProduct (v : ℝ × ℝ) : ℝ := Real.sinh |v.1| * Real.sinh |v.2|
def realSubcritical : Set (ℝ × ℝ) := {v | realProduct v < 1}
def regularRealSubcritical : Set (ℝ × ℝ) := {v | realProduct v < 1 ∧ v.1 ≠ 0 ∧ v.2 ≠ 0}

@[fun_prop] theorem realProduct_continuous : Continuous realProduct := by unfold realProduct; fun_prop

theorem realSubcritical_isOpen : IsOpen realSubcritical := isOpen_lt realProduct_continuous continuous_const

theorem realSubcritical_subset_closure_regular : realSubcritical ⊆ closure regularRealSubcritical := by
  intro v hv
  apply mem_closure_iff.mpr
  intro U hU hvU
  have hd := (dense_compl_singleton (0:ℝ)).prod (dense_compl_singleton (0:ℝ))
  obtain ⟨w,hw,hn⟩ := hd.inter_open_nonempty (U ∩ realSubcritical)
    (hU.inter realSubcritical_isOpen) ⟨v,hvU,hv⟩
  refine ⟨w,?_,?_⟩
  · exact hw.1
  · exact ⟨hw.2,hn.1,hn.2⟩

theorem realProduct_scale_lt {v : ℝ × ℝ} (hv : realProduct v ≤ 1)
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1) : realProduct (t*v.1,t*v.2) < 1 := by
  by_cases h₁ : v.1 = 0
  · simp [realProduct,h₁]
  by_cases h₂ : v.2 = 0
  · simp [realProduct,h₂]
  have ha := abs_pos.mpr h₁
  have hb := abs_pos.mpr h₂
  have hta : t*|v.1| < |v.1| := by nlinarith
  have htb : t*|v.2| < |v.2| := by nlinarith
  have hsa := Real.sinh_lt_sinh.mpr hta
  have hsb := Real.sinh_lt_sinh.mpr htb
  have hnonneg : 0 < Real.sinh (t*|v.2|) := Real.sinh_pos_iff.mpr (mul_pos ht hb)
  have hpos : 0 < Real.sinh |v.1| := Real.sinh_pos_iff.mpr ha
  have hmul := mul_lt_mul hsa hsb.le hnonneg hpos.le
  dsimp [realProduct] at hv ⊢
  rw [abs_mul,abs_mul,abs_of_pos ht]
  exact hmul.trans_le hv

theorem realProduct_le_one_mem_closure_regular {v : ℝ × ℝ} (hv : realProduct v ≤ 1) :
    v ∈ closure regularRealSubcritical := by
  have hlim : Tendsto (fun t : ℝ => (t*v.1,t*v.2)) (𝓝[<] 1) (𝓝 v) := by
    simpa using (show Continuous (fun t : ℝ => (t*v.1,t*v.2)) by fun_prop).tendsto (1:ℝ) |>.mono_left nhdsWithin_le_nhds
  have hmem : ∀ᶠ t : ℝ in 𝓝[<] 1, (t*v.1,t*v.2) ∈ closure regularRealSubcritical := by
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0:ℝ)<1)] with t ht
    exact realSubcritical_subset_closure_regular (realProduct_scale_lt hv ht.1 ht.2)
  exact isClosed_closure.mem_of_tendsto hlim hmem

end
end IsingBulk.Joint
