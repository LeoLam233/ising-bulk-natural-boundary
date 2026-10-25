import IsingBulk.Joint.Geometry.HighTopology

namespace IsingBulk.Joint
noncomputable section
open ContinuousMap

theorem cosh_tanh_mono {x u X U : ℝ} (hx : 0 ≤ x) (hu : 0 ≤ u)
    (hX : x ≤ X) (hU : u ≤ U) :
    Real.cosh x * Real.tanh u ≤ Real.cosh X * Real.tanh U := by
  have hc : Real.cosh x ≤ Real.cosh X := by
    rw [Real.cosh_le_cosh, abs_of_nonneg hx, abs_of_nonneg (hx.trans hX)]
    exact hX
  have ht := IsingBulk.Anisotropic.tanh_strictMono.monotone hU
  have hn : 0 ≤ Real.tanh u := by
    simpa using IsingBulk.Anisotropic.tanh_strictMono.monotone hu
  exact mul_le_mul hc ht hn (Real.cosh_pos _).le

theorem lowDomain_mono_re {K L : Coupling} (hK : K ∈ lowDomain)
    (h₁ : K.1.re ≤ L.1.re) (h₂ : K.2.re ≤ L.2.re)
    (hi₁ : K.1.im = L.1.im) (hi₂ : K.2.im = L.2.im) : L ∈ lowDomain := by
  refine ⟨lt_of_lt_of_le hK.1 h₁,lt_of_lt_of_le hK.2.1 h₂,?_,?_⟩
  · rw [← hi₁]
    exact lt_of_lt_of_le hK.2.2.1 (cosh_tanh_mono hK.1.le hK.2.1.le h₁ h₂)
  · rw [← hi₂]
    exact lt_of_lt_of_le hK.2.2.2 (cosh_tanh_mono hK.2.1.le hK.1.le h₂ h₁)

theorem mem_lowDomain_of_two_le {K : Coupling} (h₁ : 2 ≤ K.1.re) (h₂ : 2 ≤ K.2.re) :
    K ∈ lowDomain := by
  have ht : (1:ℝ) < Real.cosh 2 * Real.tanh 2 := by
    rw [Real.tanh_eq_sinh_div_cosh, mul_div_cancel₀ _ (Real.cosh_pos 2).ne']
    have h := Real.self_le_sinh_iff.mpr (by norm_num : (0:ℝ)≤2)
    linarith
  have hm₁ := cosh_tanh_mono (by norm_num : (0:ℝ)≤2) (by norm_num : (0:ℝ)≤2) h₁ h₂
  have hm₂ := cosh_tanh_mono (by norm_num : (0:ℝ)≤2) (by norm_num : (0:ℝ)≤2) h₂ h₁
  exact ⟨by linarith,by linarith,
    lt_of_le_of_lt (Real.abs_cos_le_one _) (ht.trans_le hm₁),
    lt_of_le_of_lt (Real.abs_cos_le_one _) (ht.trans_le hm₂)⟩

def raiseLow (K : Coupling) : Coupling :=
  (((max (2:ℝ) K.1.re : ℝ) : ℂ) + K.1.im*Complex.I,
   ((max (2:ℝ) K.2.re : ℝ) : ℂ) + K.2.im*Complex.I)

@[fun_prop] theorem raiseLow_continuous : Continuous raiseLow := by unfold raiseLow; fun_prop

theorem raiseLow_mem (K : Coupling) : raiseLow K ∈ lowDomain := by
  apply mem_lowDomain_of_two_le <;> simp [raiseLow]

def raisedLowMap : C(lowDomain,lowDomain) :=
  ⟨fun K => ⟨raiseLow K,raiseLow_mem K⟩,
    Continuous.subtype_mk (raiseLow_continuous.comp continuous_subtype_val) _⟩

def lowCenter : lowDomain := ⟨((2:ℂ),(2:ℂ)),mem_lowDomain_of_two_le (by norm_num) (by norm_num)⟩

theorem raise_segment_mem {K : Coupling} (hK : K ∈ lowDomain) {t : ℝ} (ht : 0 ≤ t) :
    K + t • (raiseLow K - K) ∈ lowDomain := by
  apply lowDomain_mono_re hK
  · simp [raiseLow]
    nlinarith [le_max_right (2:ℝ) K.1.re]
  · simp [raiseLow]
    nlinarith [le_max_right (2:ℝ) K.2.re]
  · simp [raiseLow]
  · simp [raiseLow]

def raiseLowHomotopy : Homotopy (ContinuousMap.id lowDomain) raisedLowMap where
  toFun q := ⟨q.2.val + q.1.val • (raiseLow q.2.val - q.2.val),raise_segment_mem q.2.property q.1.property.1⟩
  continuous_toFun := by fun_prop
  map_zero_left := by intro K; apply Subtype.ext; simp
  map_one_left := by intro K; apply Subtype.ext; simp [raisedLowMap]

theorem raised_center_segment_mem (K : Coupling) {t : ℝ} (_ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (1-t) • raiseLow K + t • ((2:ℂ),(2:ℂ)) ∈ lowDomain := by
  apply mem_lowDomain_of_two_le
  · simp [raiseLow]
    nlinarith [mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr (le_max_left (2:ℝ) K.1.re))]
  · simp [raiseLow]
    nlinarith [mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr (le_max_left (2:ℝ) K.2.re))]

def lowerToCenterHomotopy : Homotopy raisedLowMap (ContinuousMap.const lowDomain lowCenter) where
  toFun q := ⟨(1-q.1.val) • raiseLow q.2.val + q.1.val • ((2:ℂ),(2:ℂ)),
    raised_center_segment_mem q.2.val q.1.property.1 q.1.property.2⟩
  continuous_toFun := by fun_prop
  map_zero_left := by intro K; apply Subtype.ext; simp [raisedLowMap]
  map_one_left := by intro K; apply Subtype.ext; simp [lowCenter]

theorem lowDomain_contractible : ContractibleSpace lowDomain :=
  (contractible_iff_id_nullhomotopic lowDomain).mpr
    ⟨lowCenter,⟨raiseLowHomotopy.trans lowerToCenterHomotopy⟩⟩

end
end IsingBulk.Joint
