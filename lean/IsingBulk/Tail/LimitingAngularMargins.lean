import IsingBulk.Tail.RadialDispersionTransfer

/-! Explicit nonbranch margins on the actual limiting angular support,
not on an abstract sector label. Both branch signs are excluded by distance. -/
namespace IsingBulk.Tail
noncomputable section

theorem limiting_angular_nonbranch_margins (b h : ℝ)
    (hb : 0 < b) (hbπ : b < Real.pi) (hh : 0 < h)
    (hhb : h < b) (hhπ : b+h < Real.pi) :
    ∃ d : ℝ, 0 < d ∧ d ≤ 1 ∧ ∀ θ : ℝ, |θ| ≤ Real.pi →
      (d ≤ limitingAngularW b θ+1) ∧ |limitingAngularW b θ| ≤ 3 ∧
      (h ≤ |(|θ|-b)| → d ≤ |limitingAngularW b θ-1|) := by
  let gL := Real.cos b-Real.cos (b+h)
  let gR := Real.cos (b-h)-Real.cos b
  have hgL : 0 < gL := by
    apply sub_pos.mpr
    exact Real.strictAntiOn_cos ⟨hb.le,hbπ.le⟩ ⟨by linarith,hhπ.le⟩ (by linarith)
  have hgR : 0 < gR := by
    apply sub_pos.mpr
    exact Real.strictAntiOn_cos ⟨by linarith,by linarith⟩ ⟨hb.le,hbπ.le⟩ (by linarith)
  have hS : 0 < 1+Real.cos b := by
    have he := Real.strictAntiOn_cos ⟨hb.le,hbπ.le⟩
      ⟨Real.pi_pos.le,le_rfl⟩ hbπ
    simp only [Real.cos_pi] at he
    linarith
  let d := min 1 (min gL (min gR (1+Real.cos b)))
  have hd : 0 < d := lt_min zero_lt_one (lt_min hgL (lt_min hgR hS))
  have hds : d ≤ 1 ∧ d ≤ gL ∧ d ≤ gR ∧ d ≤ 1+Real.cos b := by
    have he : d ≤ min 1 (min gL (min gR (1+Real.cos b))) := le_rfl
    simpa only [le_min_iff] using he
  refine ⟨d,hd,hds.1,?_⟩
  intro θ hθ
  have hwlo : 1+Real.cos b ≤ limitingAngularW b θ+1 := by
    unfold limitingAngularW
    linarith [Real.cos_le_one θ]
  have hwabs : |limitingAngularW b θ| ≤ 3 := by
    rw [abs_le]
    unfold limitingAngularW
    constructor <;> linarith [Real.neg_one_le_cos θ,Real.cos_le_one θ,
      Real.neg_one_le_cos b,Real.cos_le_one b]
  refine ⟨hds.2.2.2.trans hwlo,hwabs,?_⟩
  intro hsep
  have hcθ : Real.cos |θ|=Real.cos θ := Real.cos_abs θ
  by_cases hinner : |θ| ≤ b
  · rw [abs_of_nonpos (sub_nonpos.mpr hinner)] at hsep
    have hcos : Real.cos (b-h) ≤ Real.cos θ := by
      rw [← hcθ]
      exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg θ) (by linarith)
        (by linarith)
    have he : gR ≤ |limitingAngularW b θ-1| := by
      unfold gR limitingAngularW
      have ha := neg_le_abs (Real.cos b-Real.cos θ)
      have he : 1+Real.cos b-Real.cos θ-1=Real.cos b-Real.cos θ := by ring
      rw [he]
      linarith
    exact hds.2.2.1.trans he
  · have hout : b ≤ |θ| := le_of_not_ge hinner
    rw [abs_of_nonneg (sub_nonneg.mpr hout)] at hsep
    have hcos : Real.cos θ ≤ Real.cos (b+h) := by
      rw [← hcθ]
      exact Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) hθ (by linarith)
    have he : gL ≤ |limitingAngularW b θ-1| := by
      unfold gL limitingAngularW
      have ha := le_abs_self (Real.cos b-Real.cos θ)
      have he : 1+Real.cos b-Real.cos θ-1=Real.cos b-Real.cos θ := by ring
      rw [he]
      linarith
    exact hds.2.1.trans he

end
end IsingBulk.Tail
