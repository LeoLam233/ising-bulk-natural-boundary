import IsingBulk.Preferred22.ShellObligations
import IsingBulk.Preferred22.ContourBumpJets
import Mathlib.Data.Nat.Choose.Multinomial

/-! Uniform real angular jets of the actual smooth transport cutoffs.
No cutoff is treated as a holomorphic function. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set Filter
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false

/-- The literal population selector has bounded derivatives of every fixed
order on the entire real line, using its two actual constant tails. -/
theorem preferredPopulationCutoff_global_jet (j : ℕ) :
    ∃ C : ℝ,1≤C ∧ ∀ x : ℝ, ‖iteratedFDeriv ℝ j preferredPopulationCutoff x‖≤C := by
  obtain ⟨A,hA⟩ := (isCompact_Icc : IsCompact (Icc (0:ℝ) 1)).exists_bound_of_continuousOn
    (preferredPopulationCutoff_smooth.continuous_iteratedFDeriv (by simp)).continuousOn
  refine ⟨max A 1,le_max_right _ _,?_⟩
  intro x
  by_cases hlo : 0≤x
  · by_cases hhi : x≤1
    · exact (hA x ⟨hlo,hhi⟩).trans (le_max_left _ _)
    · have hx : 1<x := lt_of_not_ge hhi
      have he : preferredPopulationCutoff =ᶠ[𝓝 x] (fun _ : ℝ => (1:ℝ)) := by
        filter_upwards [(show ∀ᶠ y : ℝ in 𝓝 x, 1/2<y from Ioi_mem_nhds (by linarith))] with y hy
        exact preferredPopulationCutoff_one hy.le
      rw [(he.iteratedFDeriv ℝ j).eq_of_nhds]
      cases j with
      | zero => simpa only [norm_iteratedFDeriv_zero,norm_one] using le_max_right A 1
      | succ j => simp only [iteratedFDeriv_succ_const,Pi.zero_apply,norm_zero]; exact (zero_le_one.trans (le_max_right A 1))
  · have hx : x<0 := lt_of_not_ge hlo
    have he : preferredPopulationCutoff =ᶠ[𝓝 x] (fun _ : ℝ => (0:ℝ)) := by
      filter_upwards [(show ∀ᶠ y : ℝ in 𝓝 x, y<1/4 from Iio_mem_nhds (by linarith))] with y hy
      exact preferredPopulationCutoff_zero hy.le
    rw [(he.iteratedFDeriv ℝ j).eq_of_nhds]
    cases j with
    | zero => simp only [norm_iteratedFDeriv_zero,norm_zero]; exact zero_le_one.trans (le_max_right A 1)
    | succ j => simp only [iteratedFDeriv_succ_const,Pi.zero_apply,norm_zero]; exact zero_le_one.trans (le_max_right A 1)

theorem preferredPopulationCutoff_finite_jets (J : ℕ) :
    ∃ C : ℝ,1≤C ∧ ∀ j≤J, ∀ x : ℝ, ‖iteratedFDeriv ℝ j preferredPopulationCutoff x‖≤C := by
  choose A hA hbound using preferredPopulationCutoff_global_jet
  let C := 1+∑ j ∈ Finset.range (J+1), A j
  have hsum : 0≤∑ j ∈ Finset.range (J+1), A j := Finset.sum_nonneg (fun j _ => zero_le_one.trans (hA j))
  refine ⟨C,by dsimp [C]; linarith,?_⟩
  intro j hj x
  apply (hbound j x).trans
  have hh := Finset.single_le_sum (fun r (_ : r∈Finset.range (J+1)) => zero_le_one.trans (hA r))
    (show j∈Finset.range (J+1) from Finset.mem_range.mpr (by omega))
  dsimp [C]
  linarith

/-- Unnormalized occupancies cost only one factor N in every fixed real
angular derivative, including the order-zero bound. -/
theorem preferred_occupancy_jet_le {N j : ℕ} (p : ℝ → ℝ) (hp : ContDiff ℝ ∞ p)
    {B : ℝ} (hB : 0≤B) (hb : ∀ x, ‖iteratedFDeriv ℝ j p x‖≤B) (θ : Fin N → ℝ) :
    ‖iteratedFDeriv ℝ j (@occupancy N p) θ‖≤(N:ℝ)*B := by
  have hs (i : Fin N) : ContDiff ℝ ∞ (fun x : Fin N → ℝ => p (x i)) := by fun_prop
  change ‖iteratedFDeriv ℝ j (fun x : Fin N → ℝ => ∑ i, p (x i)) θ‖≤_
  rw [iteratedFDeriv_fun_sum_apply (fun i _ => ((hs i).of_le (by simp)).contDiffAt)]
  exact (norm_sum_le _ _).trans (by
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using
      Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => coordinate_real_jet_le p hp hB hb i θ))

/-- The actual population cutoff composed with P or Q has only a polynomial
in N cost. All real cutoff derivatives are retained. -/
theorem preferred_population_composition_jet (p : ℝ → ℝ) (hp : ContDiff ℝ ∞ p)
    (hper : Function.Periodic p (2*Real.pi)) (j : ℕ) :
    ∃ C : ℝ,0<C ∧ ∀ N : ℕ,0<N → ∀ θ : Fin N → ℝ,
      ‖iteratedFDeriv ℝ j (fun x : Fin N → ℝ => preferredPopulationCutoff (occupancy p x)) θ‖≤C*(N:ℝ)^j := by
  obtain ⟨A,hA,hη⟩ := preferredPopulationCutoff_finite_jets j
  obtain ⟨B,hB,hpjet⟩ := bump_finite_jets p hp hper j
  let D := max B 1
  have hD : 1≤D := le_max_right _ _
  have hD0 : 0<D := zero_lt_one.trans_le hD
  refine ⟨(j.factorial:ℝ)*A*D^j,by positivity,?_⟩
  intro N hN θ
  have hn : (1:ℝ)≤N := by exact_mod_cast hN
  have hocc : ContDiff ℝ ∞ (@occupancy N p) := by unfold occupancy; fun_prop
  have hND : 1≤(N:ℝ)*D := by nlinarith
  have hh := norm_iteratedFDeriv_comp_le preferredPopulationCutoff_smooth hocc
    (by simp : (j:ℕ∞ω)≤∞) θ (fun k hk => hη k hk _)
    (D := (N:ℝ)*D) (fun k hk hkj =>
      (preferred_occupancy_jet_le p hp hB.le (hpjet k hkj) θ).trans
        ((mul_le_mul_of_nonneg_left (le_max_left B 1) (Nat.cast_nonneg N)).trans
          (le_self_pow₀ hND (by omega : k≠0))))
  apply hh.trans_eq
  rw [mul_pow]
  ring

theorem preferred_population_composition_finite_jets (p : ℝ → ℝ) (hp : ContDiff ℝ ∞ p)
    (hper : Function.Periodic p (2*Real.pi)) (J : ℕ) :
    ∃ C : ℝ,1≤C ∧ ∀ N : ℕ,0<N → ∀ θ : Fin N → ℝ, ∀ j≤J,
      ‖iteratedFDeriv ℝ j (fun x : Fin N → ℝ => preferredPopulationCutoff (occupancy p x)) θ‖≤C*(N:ℝ)^J := by
  choose A hA hj using preferred_population_composition_jet p hp hper
  let C := 1+∑ j ∈ Finset.range (J+1), A j
  have hsum : 0≤∑ j ∈ Finset.range (J+1), A j := Finset.sum_nonneg (fun j _ => (hA j).le)
  refine ⟨C,by dsimp [C]; linarith,?_⟩
  intro N hN θ j hjJ
  have hn : (1:ℝ)≤N := by exact_mod_cast hN
  have hAj : A j≤C := by
    have hh := Finset.single_le_sum (fun k (_ : k∈Finset.range (J+1)) => (hA k).le)
      (show j∈Finset.range (J+1) from Finset.mem_range.mpr (by omega))
    dsimp [C]
    linarith
  exact (hj j N hN θ).trans (mul_le_mul hAj (pow_le_pow_right₀ hn hjJ)
    (by positivity) (by dsimp [C]; positivity))

/-- Exact multinomial counting bounds every fixed jet of a finite product
without an extra factorial in the number of factors. -/
theorem preferred_finite_product_jet_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {N j : ℕ} (f : Fin N → E → ℝ) (hf : ∀ i, ContDiff ℝ ∞ (f i)) (x : E)
    {B : ℝ} (_hB : 0≤B) (hjet : ∀ i, ∀ k≤j, ‖iteratedFDeriv ℝ k (f i) x‖≤B) :
    ‖iteratedFDeriv ℝ j (fun y => ∏ i, f i y) x‖≤(N:ℝ)^j*B^N := by
  have hh := norm_iteratedFDeriv_prod_le (u := Finset.univ) (fun i _ => hf i)
    (x := x) (by simp : (j:ℕ∞ω)≤∞)
  have hc : (∑ a∈(Finset.univ : Finset (Fin N)).sym j, (a.val.countPerms:ℝ))=(N:ℝ)^j := by
    simpa using (Finset.sum_pow (s := (Finset.univ : Finset (Fin N))) (fun _ : Fin N => (1:ℝ)) j).symm
  apply hh.trans
  calc
    _ ≤ ∑ a∈(Finset.univ : Finset (Fin N)).sym j, (a.val.countPerms:ℝ)*B^N := by
      apply Finset.sum_le_sum
      intro a _
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      calc
        _ ≤ ∏ _i : Fin N, B := by
          apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
          intro i _
          apply hjet i _
          exact (Multiset.count_le_card i a.val).trans_eq a.property
        _ = B^N := by simp
    _ = _ := by rw [← Finset.sum_mul,hc]

/-- The complete right telescope product has the source-allowed C^N N^j
real angular jet bound, uniformly in particle number. -/
theorem preferredRightWeight_finite_jets (r : ℝ → ℝ) (hr : ContDiff ℝ ∞ r)
    (hper : Function.Periodic r (2*Real.pi)) (J : ℕ) :
    ∃ C : ℝ,1≤C ∧ ∀ N : ℕ,0<N → ∀ θ : Fin N → ℝ, ∀ j≤J,
      ‖iteratedFDeriv ℝ j (@preferredRightWeight N r) θ‖≤C^N*(N:ℝ)^J := by
  obtain ⟨B,hB,hjets⟩ := bump_finite_jets r hr hper J
  let C := max B 1
  have hC : 1≤C := le_max_right _ _
  refine ⟨C,hC,?_⟩
  intro N hN θ j hjJ
  have hn : (1:ℝ)≤N := by exact_mod_cast hN
  have hh := preferred_finite_product_jet_le (fun (i : Fin N) (x : Fin N → ℝ) => r (x i))
    (fun i => by fun_prop) θ (B := C) (zero_le_one.trans hC)
    (fun i k hk => (coordinate_real_jet_le r hr hB.le (hjets k (hk.trans hjJ)) i θ).trans (le_max_left _ _))
  apply hh.trans
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hn hjJ) (by positivity)

private theorem preferred_real_add_jet_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f g : E → ℝ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x : E) (j : ℕ)
    {B D : ℝ} (hb : ‖iteratedFDeriv ℝ j f x‖≤B) (hd : ‖iteratedFDeriv ℝ j g x‖≤D) :
    ‖iteratedFDeriv ℝ j (fun y => f y+g y) x‖≤B+D := by
  rw [fun_iteratedFDeriv_add_apply (hf.of_le (by simp)).contDiffAt (hg.of_le (by simp)).contDiffAt]
  exact (norm_add_le _ _).trans (add_le_add hb hd)

private theorem preferred_constant_one_jet_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (j : ℕ) (x : E) : ‖iteratedFDeriv ℝ j (fun _ : E => (1:ℝ)) x‖≤1 := by
  cases j with
  | zero => simp
  | succ j => simp only [iteratedFDeriv_succ_const,Pi.zero_apply,norm_zero]; norm_num

/-- The genuine lower population weight, including both independent
occupancy sums, has polynomial particle-number jets. -/
theorem preferredLowerWeight_finite_jets (p m : ℝ → ℝ) (hp : ContDiff ℝ ∞ p)
    (hm : ContDiff ℝ ∞ m) (hpp : Function.Periodic p (2*Real.pi))
    (hmp : Function.Periodic m (2*Real.pi)) (J : ℕ) :
    ∃ C : ℝ,1≤C ∧ ∀ N : ℕ,0<N → ∀ θ : Fin N → ℝ, ∀ j≤J,
      ‖iteratedFDeriv ℝ j (@preferredLowerWeight N preferredPopulationCutoff p m) θ‖≤C*(N:ℝ)^(2*J) := by
  obtain ⟨Cp,hCp,hpjet⟩ := preferred_population_composition_finite_jets p hp hpp J
  obtain ⟨Cm,hCm,hmjet⟩ := preferred_population_composition_finite_jets m hm hmp J
  let B := max Cp Cm
  have hB : 1≤B := hCp.trans (le_max_left _ _)
  let C := 1+2^J*(1+B)^2
  have hC : 1≤C := by
    dsimp [C]
    have : (0:ℝ)≤2^J*(1+B)^2 := by positivity
    linarith
  refine ⟨C,hC,?_⟩
  intro N hN θ j hj
  have hn : (1:ℝ)≤N := by exact_mod_cast hN
  have hnJ : 1≤(N:ℝ)^J := one_le_pow₀ hn
  let f := fun x : Fin N → ℝ => 1-preferredPopulationCutoff (occupancy p x)
  let g := fun x : Fin N → ℝ => 1+preferredPopulationCutoff (occupancy m x)
  have hfp : ContDiff ℝ ∞ (fun x : Fin N → ℝ => preferredPopulationCutoff (occupancy p x)) := by
    apply preferredPopulationCutoff_smooth.comp
    unfold occupancy
    fun_prop
  have hgm : ContDiff ℝ ∞ (fun x : Fin N → ℝ => preferredPopulationCutoff (occupancy m x)) := by
    apply preferredPopulationCutoff_smooth.comp
    unfold occupancy
    fun_prop
  have hf : ContDiff ℝ ∞ f := contDiff_const.sub hfp
  have hg : ContDiff ℝ ∞ g := contDiff_const.add hgm
  have hfjet (k : ℕ) (hk : k≤J) : ‖iteratedFDeriv ℝ k f θ‖≤(1+B)*(N:ℝ)^J := by
    have hh := real_difference_jet_le (fun _ : Fin N → ℝ => (1:ℝ)) _ contDiff_const hfp θ k
      (preferred_constant_one_jet_le k θ) (hpjet N hN θ k hk)
    apply hh.trans
    have hb : Cp*(N:ℝ)^J≤B*(N:ℝ)^J := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    nlinarith
  have hgjet (k : ℕ) (hk : k≤J) : ‖iteratedFDeriv ℝ k g θ‖≤(1+B)*(N:ℝ)^J := by
    have hh := preferred_real_add_jet_le (fun _ : Fin N → ℝ => (1:ℝ)) _ contDiff_const hgm θ k
      (preferred_constant_one_jet_le k θ) (hmjet N hN θ k hk)
    apply hh.trans
    have hb : Cm*(N:ℝ)^J≤B*(N:ℝ)^J := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
    nlinarith
  have hprod := real_two_factor_uniform_jet f g hf hg θ J j hj
    (by positivity : 0≤(1+B)*(N:ℝ)^J) (by positivity : 0≤(1+B)*(N:ℝ)^J) hfjet hgjet
  have he : @preferredLowerWeight N preferredPopulationCutoff p m=
      fun x => (1/2:ℝ) • (f x*g x) := by
    funext x
    unfold preferredLowerWeight lowerWeight f g
    simp only [smul_eq_mul]
    ring
  rw [he,iteratedFDeriv_const_smul_apply' ((hf.mul hg).of_le (by simp)).contDiffAt,norm_smul]
  have hh : ‖(1/2:ℝ)‖*‖iteratedFDeriv ℝ j (fun x => f x*g x) θ‖≤
      2^J*((1+B)*(N:ℝ)^J)*((1+B)*(N:ℝ)^J) :=
    (mul_le_of_le_one_left (norm_nonneg _) (by norm_num)).trans hprod
  apply hh.trans
  calc
    _ = (2^J*(1+B)^2)*(N:ℝ)^(2*J) := by rw [pow_mul]; ring
    _ ≤ C*(N:ℝ)^(2*J) := by dsimp [C]; gcongr; linarith

/-- The actual source cell weight carries C_J^N times a polynomial in N
under every fixed real angular jet. The population selector, both actual
occupancies and the full telescope product all remain literal. -/
theorem preferredCellWeight_right_finite_jets (p m r : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m) (hr : ContDiff ℝ ∞ r)
    (hpp : Function.Periodic p (2*Real.pi)) (hmp : Function.Periodic m (2*Real.pi))
    (hrp : Function.Periodic r (2*Real.pi)) (J : ℕ) :
    ∃ C : ℝ,1≤C ∧ ∀ N : ℕ,0<N → ∀ θ : Fin N → ℝ, ∀ j≤J,
      ‖iteratedFDeriv ℝ j (preferredCellWeight .right preferredPopulationCutoff p m r : (Fin N → ℝ) → ℝ) θ‖≤
        C^N*(N:ℝ)^(3*J) := by
  obtain ⟨L,hL,hLjet⟩ := preferredLowerWeight_finite_jets p m hp hm hpp hmp J
  obtain ⟨R,hR,hRjet⟩ := preferredRightWeight_finite_jets r hr hrp J
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
  intro N hN θ j hj
  have hη := preferredPopulationCutoff_smooth
  have hleft : ContDiff ℝ ∞ (@preferredLowerWeight N preferredPopulationCutoff p m) := by
    unfold preferredLowerWeight lowerWeight occupancy
    fun_prop
  have hright : ContDiff ℝ ∞ (@preferredRightWeight N r) := by
    unfold preferredRightWeight
    fun_prop
  have hh := real_two_factor_uniform_jet (@preferredLowerWeight N preferredPopulationCutoff p m)
    (@preferredRightWeight N r) hleft hright θ J j hj
    (by positivity : 0≤L*(N:ℝ)^(2*J)) (by positivity : 0≤R^N*(N:ℝ)^J)
    (hLjet N hN θ) (hRjet N hN θ)
  change ‖iteratedFDeriv ℝ j (fun x => preferredLowerWeight preferredPopulationCutoff p m x*
    preferredRightWeight r x) θ‖≤_
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
