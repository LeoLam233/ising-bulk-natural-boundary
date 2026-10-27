import IsingBulk.Preferred22.CutoffJets

/-! Real angular derivatives of the literal named-anchor telescope weight.
The named anchor is fixed throughout differentiation. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set Filter
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false

private theorem preferred_anchor_constant_one_jet_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (j : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ j (fun _ : E => (1:ℝ)) x‖≤1 := by
  cases j with
  | zero => simp
  | succ j => simp only [iteratedFDeriv_succ_const,Pi.zero_apply,norm_zero]; norm_num

/-- A fixed named-anchor weight is a product of N genuine smooth scalar
factors. Its finite real jets have no factorial particle cost. -/
theorem preferredAnchorWeight_finite_jets (r : ℝ → ℝ) (hr : ContDiff ℝ ∞ r)
    (hper : Function.Periodic r (2*Real.pi)) (J : ℕ) :
    ∃ C : ℝ,1≤C ∧ ∀ N : ℕ,0<N → ∀ θ : Fin N → ℝ,∀ a : Fin N,∀ j≤J,
      ‖iteratedFDeriv ℝ j (fun x => preferredAnchorWeight r x a) θ‖≤C^N*(N:ℝ)^J := by
  classical
  obtain ⟨B,hB,hjets⟩ := bump_finite_jets r hr hper J
  let C := 1+B
  have hC : 1≤C := by dsimp [C]; linarith
  refine ⟨C,hC,?_⟩
  intro N hN θ a j hj
  have hn : (1:ℝ)≤N := by exact_mod_cast hN
  let f : Fin N → (Fin N → ℝ) → ℝ := fun i x =>
    if i=a then 1-r (x i) else if i<a then r (x i) else 1
  have hf (i : Fin N) : ContDiff ℝ ∞ (f i) := by
    by_cases hia : i=a
    · simp only [f,ite_eq_left hia]
      fun_prop
    · simp only [f,ite_eq_right hia]
      by_cases hil : i<a
      · simp only [ite_eq_left hil]
        fun_prop
      · simp only [ite_eq_right hil]
        fun_prop
  have he : (fun x : Fin N → ℝ => preferredAnchorWeight r x a)=fun x => ∏ i,f i x := by
    funext x
    have hh : (∏ i,f i x)=
        ∏ i : Fin N,(if i=a then 1-r (x i) else 1)*(if i<a then r (x i) else 1) := by
      apply Finset.prod_congr rfl
      intro i _
      by_cases hia : i=a
      · subst i
        simp only [f,ite_true,lt_self_iff_false,ite_false,mul_one]
      · simp only [f,ite_eq_right hia,one_mul]
    rw [hh,Finset.prod_mul_distrib,Fintype.prod_ite_eq']
    unfold preferredAnchorWeight
    congr 1
    rw [Finset.prod_filter]
  have hfj (i : Fin N) (k : ℕ) (hk : k≤j) :
      ‖iteratedFDeriv ℝ k (f i) θ‖≤C := by
    have hrcoord : ContDiff ℝ ∞ (fun x : Fin N → ℝ => r (x i)) := by fun_prop
    have hb := coordinate_real_jet_le r hr hB.le (hjets k (hk.trans hj)) i θ
    by_cases hia : i=a
    · simp only [f,ite_eq_left hia]
      exact real_difference_jet_le (fun _ : Fin N → ℝ => (1:ℝ)) _ contDiff_const hrcoord θ k
        (preferred_anchor_constant_one_jet_le k θ) hb
    · simp only [f,ite_eq_right hia]
      by_cases hil : i<a
      · simp only [ite_eq_left hil]
        exact hb.trans (by dsimp [C]; linarith)
      · simp only [ite_eq_right hil]
        exact (preferred_anchor_constant_one_jet_le k θ).trans hC
  rw [he]
  have hh := preferred_finite_product_jet_le f hf θ (B:=C) (zero_le_one.trans hC) hfj
  exact hh.trans (by rw [mul_comm]; exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hn hj) (by positivity))

/-- The complete lower population selector times the fixed named-anchor
weight retains the source C_J^N N^(3J) bound in real angular coordinates. -/
theorem preferredCellWeight_anchor_finite_jets (p m r : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m) (hr : ContDiff ℝ ∞ r)
    (hpp : Function.Periodic p (2*Real.pi)) (hmp : Function.Periodic m (2*Real.pi))
    (hrp : Function.Periodic r (2*Real.pi)) (J : ℕ) :
    ∃ C : ℝ,1≤C ∧ ∀ N : ℕ,0<N → ∀ θ : Fin N → ℝ,∀ a : Fin N,∀ j≤J,
      ‖iteratedFDeriv ℝ j (preferredCellWeight (.anchor a) preferredPopulationCutoff p m r) θ‖≤
        C^N*(N:ℝ)^(3*J) := by
  obtain ⟨L,hL,hLjet⟩ := preferredLowerWeight_finite_jets p m hp hm hpp hmp J
  obtain ⟨R,hR,hRjet⟩ := preferredAnchorWeight_finite_jets r hr hrp J
  let A := 1+2^J*L+R
  have hA : 1≤A := by
    dsimp [A]
    have : (0:ℝ)≤2^J*L := by positivity
    linarith
  have hAL : 2^J*L≤A := by dsimp [A]; linarith
  have hAR : R≤A := by
    dsimp [A]
    have : (0:ℝ)≤2^J*L := by positivity
    linarith
  refine ⟨A^2,one_le_pow₀ hA,?_⟩
  intro N hN θ a j hj
  have hη := preferredPopulationCutoff_smooth
  have hleft : ContDiff ℝ ∞ (@preferredLowerWeight N preferredPopulationCutoff p m) := by
    unfold preferredLowerWeight lowerWeight occupancy
    fun_prop
  have hanchor : ContDiff ℝ ∞ (fun x : Fin N → ℝ => preferredAnchorWeight r x a) := by
    unfold preferredAnchorWeight
    fun_prop
  have hh := real_two_factor_uniform_jet (@preferredLowerWeight N preferredPopulationCutoff p m)
    (fun x => preferredAnchorWeight r x a) hleft hanchor θ J j hj
    (by positivity : 0≤L*(N:ℝ)^(2*J)) (by positivity : 0≤R^N*(N:ℝ)^J)
    (hLjet N hN θ) (hRjet N hN θ a)
  change ‖iteratedFDeriv ℝ j (fun x => preferredLowerWeight preferredPopulationCutoff p m x*
    preferredAnchorWeight r x a) θ‖≤_
  apply hh.trans
  calc
    _ = (2^J*L)*R^N*(N:ℝ)^(3*J) := by
      rw [show 3*J=2*J+J by omega,pow_add]
      ring
    _ ≤ A^N*A^N*(N:ℝ)^(3*J) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul (hAL.trans (le_self_pow₀ hA (by omega : N≠0)))
        (pow_le_pow_left₀ (zero_le_one.trans hR) hAR N) (by positivity) (by positivity)
    _ = (A^2)^N*(N:ℝ)^(3*J) := by rw [pow_two,mul_pow]

end
end IsingBulk.Preferred22
