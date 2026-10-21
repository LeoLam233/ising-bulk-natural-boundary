import IsingBulk.HT.First.OddSchur
import IsingBulk.Tail.WeightedAngularPfaffian
import IsingBulk.Tail.ExteriorPairBridge
import Mathlib.Data.List.OfFn

/-!
# Odd-particle matching adapters

The ghost is a constant algebraic variable; it is not another Ising particle.
The dummy integration identity below is useful for applying the existing
coupled even-Pfaffian estimate without discarding occupancy dependence.
-/
namespace IsingBulk.HT.Contour
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.Schur MeasureTheory
open scoped BigOperators

/-- The odd factorial normalization cancels the augmented matching count. -/
theorem odd_matchingCount_factorial (n : ℕ) :
    matchingCount (n+1) * (2^n * n.factorial) = (2*n+1).factorial := by
  rw [matchingCount, Nat.factorial_succ]
  calc
    (2*n+1) * matchingCount n * (2^n * n.factorial) =
        (2*n+1) * (matchingCount n * (2^n * n.factorial)) := by ring
    _ = _ := by rw [matchingCount_factorial]

/-- All physical pairs and the unit ghost column are bounded explicitly. -/
theorem odd_pairProduct_norm_le_matchings (n : ℕ) (xs : List ℂ)
    (hlen : xs.length = 2*n+1)
    (hd : ∀ v ∈ xs, ∀ w ∈ xs, 1-v*w ≠ 0)
    (hg : ∀ v ∈ xs, v ≠ -1)
    {C : ℝ} (hC : 1 ≤ C)
    (hpair : ∀ v ∈ xs, ∀ w ∈ xs, ‖(v-w)/(1-v*w)‖ ≤ C) :
    ‖Schur.pairProduct (fun a b => (a-b)/(1-a*b)) xs‖ ≤
      (matchingCount (n+1) : ℝ) * C^(n+1) := by
  rw [← IsingBulk.HT.First.schur_odd_specialization n xs hlen hd hg]
  apply pfaffian_norm_le_matchings _ (n+1) _ (by simp only
    [List.length_append, List.length_cons, List.length_nil, hlen]; omega) (by linarith)
  intro a ha b hb
  rcases List.mem_append.mp ha with ha | ha
  · rcases List.mem_append.mp hb with hb | hb
    · exact hpair a ha b hb
    · have hb' : b = -1 := by simpa using hb
      subst b
      rw [IsingBulk.HT.First.schur_ghost_entry (hg a ha), norm_one]
      exact hC
  · have ha' : a = -1 := by simpa using ha
    subst a
    rcases List.mem_append.mp hb with hb | hb
    · have he : ((-1:ℂ)-b)/(1-(-1)*b) = -((b-(-1))/(1-b*(-1))) := by
        ring
      rw [he, norm_neg, IsingBulk.HT.First.schur_ghost_entry (hg b hb), norm_one]
      exact hC
    · have hb' : b = -1 := by simpa using hb
      subst b
      simp only [sub_self, zero_div, norm_zero]
      linarith

/-- Indexed version matching the actual complete product in the source. -/
theorem odd_indexed_pairProduct_norm_le_matchings (n : ℕ)
    (y : Fin (2*n+1) → ℂ)
    (hd : ∀ i j, 1-y i*y j ≠ 0) (hg : ∀ i, y i ≠ -1)
    {C : ℝ} (hC : 1 ≤ C) (hpair : ∀ i j, ‖pairKernel (y i) (y j)‖ ≤ C) :
    ‖First.pairProduct y‖ ≤ (matchingCount (n+1) : ℝ) * C^(n+1) := by
  rw [pairProduct_eq_schur]
  apply odd_pairProduct_norm_le_matchings n (List.ofFn y) (by simp)
  · intro v hv w hw
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hv
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hw
    exact hd i j
  · intro v hv
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hv
    exact hg i
  · exact hC
  · intro v hv w hw
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hv
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hw
    exact hpair i j

/-- Appending the fixed ghost gives exactly the augmented Pfaffian, with the
original ordering of physical coordinates retained. -/
theorem odd_pairProduct_eq_augmented (n : ℕ) (y : Fin (2*n+1) → ℂ)
    (hd : ∀ i j, 1-y i*y j ≠ 0) (hg : ∀ i, y i ≠ -1) :
    First.pairProduct y =
      labelPfaffian (fun i j => pairKernel (Fin.snoc (α := fun _ : Fin (2*n+1+1) => ℂ) y (-1) i) (Fin.snoc (α := fun _ : Fin (2*n+1+1) => ℂ) y (-1) j))
        (n+1) (List.finRange (2*n+1+1)) := by
  rw [labelPfaffian_source, ← List.ofFn_eq_map, pairProduct_eq_schur]
  have hsnoc : List.ofFn (Fin.snoc (α := fun _ : Fin (2*n+1+1) => ℂ) y (-1)) = List.ofFn y ++ [-1] := by
    rw [Fin.snoc_eq_append, List.ofFn_fin_append]
    simp
  rw [hsnoc]
  symm
  apply IsingBulk.HT.First.schur_odd_specialization n (List.ofFn y) (by simp)
  · intro v hv w hw
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hv
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hw
    exact hd i j
  · intro v hv
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hv
    exact hg i

/-- A dummy last angle factors out as its actual one-body integral.  No
independence assumption about the physical density is made: F may couple
all N physical coordinates arbitrarily. -/
theorem integral_dummy_last {E : Type*} [MeasurableSpace E]
    (N : ℕ) (μ : Measure E) [SigmaFinite μ]
    (c : E → ℝ) (F : (Fin N → E) → ℝ) :
    (∫ x : Fin (N+1) → E, c (x (Fin.last N)) * F (Fin.init x)
      ∂Measure.pi (fun _ => μ)) =
      (∫ u, c u ∂μ) * (∫ x : Fin N → E, F x ∂Measure.pi (fun _ => μ)) := by
  rw [← ((measurePreserving_piFinSuccAbove (fun _ : Fin (N+1) => μ)
    (Fin.last N)).symm).integral_comp']
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Equiv.coe_fn_mk, Fin.insertNth_last', Fin.snoc_last, Fin.init_snoc]
  exact integral_prod_mul c F

/-- Integrability also descends from the dummy-angle construction when its
one-body mass is nonzero. -/
theorem integrable_of_dummy_last {E : Type*} [MeasurableSpace E]
    (N : ℕ) (μ : Measure E) [SigmaFinite μ]
    (c : E → ℝ) (F : (Fin N → E) → ℝ)
    (h : Integrable (fun x : Fin (N+1) → E => c (x (Fin.last N))*F (Fin.init x))
      (Measure.pi (fun _ => μ))) (hmass : (∫ u, c u ∂μ) ≠ 0) :
    Integrable F (Measure.pi (fun _ => μ)) := by
  have hprod : Integrable (fun p : E × (Fin N → E) => c p.1*F p.2)
      (μ.prod (Measure.pi (fun _ => μ))) := by
    rw [← ((measurePreserving_piFinSuccAbove (fun _ : Fin (N+1) => μ)
      (Fin.last N)).symm).integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)] at h
    simpa only [Function.comp_def, MeasurableEquiv.piFinSuccAbove_symm_apply,
      Fin.insertNthEquiv, Equiv.coe_fn_mk, Fin.insertNth_last', Fin.snoc_last,
      Fin.init_snoc] using h
  by_contra hn
  have hz : ∀ᵐ u ∂μ, c u = 0 := by
    filter_upwards [hprod.prod_right_ae] with u hu
    by_contra hcu
    apply hn
    have hc := hu.const_mul (c u)⁻¹
    simpa only [← mul_assoc, inv_mul_cancel₀ hcu, one_mul] using hc
  exact hmass (integral_eq_zero_of_ae hz)

/-- Coupled odd matching bound obtained from the established even matching
integral.  The only added cost is division by the dummy one-body mass.
All physical coordinates may remain coupled through Y. -/
theorem coupled_odd_pairProduct_integrable_and_le {E : Type*} [MeasurableSpace E]
    (n : ℕ) (μ : Measure E) [SigmaFinite μ]
    (c : E → ℝ) (hc : ∀ x, 0 ≤ c x)
    (Y : (Fin (2*n+1) → E) → Fin (2*n+1) → ℂ)
    (k : E → E → ℝ) (hk : ∀ x y, 0 ≤ k x y)
    (hd : ∀ x i j, 1-Y x i*Y x j ≠ 0)
    (hg : ∀ x i, Y x i ≠ -1)
    (hA : ∀ x i j, ‖pairKernel (Y x i) (Y x j)‖ ≤ k (x i) (x j))
    (hpair : Integrable (fun v : Fin 2 → E =>
      c (v 0)*c (v 1)*(k (v 0) (v 1)+1)) (Measure.pi (fun _ => μ)))
    (hmeas : AEStronglyMeasurable (fun x : Fin (2*n+1+1) → E =>
      (∏ i,c (x i)) * ‖First.pairProduct (Y (Fin.init x))‖)
        (Measure.pi (fun _ => μ)))
    (hmass : 0 < ∫ u, c u ∂μ) :
    Integrable (fun x : Fin (2*n+1) → E => (∏ i,c (x i))*‖First.pairProduct (Y x)‖)
      (Measure.pi (fun _ => μ)) ∧
    (∫ x : Fin (2*n+1) → E, (∏ i,c (x i))*‖First.pairProduct (Y x)‖
      ∂Measure.pi (fun _ => μ)) ≤
      ((matchingCount (n+1):ℝ) *
        (∫ v : Fin 2 → E, c (v 0)*c (v 1)*(k (v 0) (v 1)+1)
          ∂Measure.pi (fun _ => μ))^(n+1)) / (∫ u, c u ∂μ) := by
  let A : (Fin (2*n+1+1) → E) → Fin (2*n+1+1) → Fin (2*n+1+1) → ℂ :=
    fun x i j => pairKernel (Fin.snoc (α := fun _ : Fin (2*n+1+1) => ℂ) (Y (Fin.init x)) (-1) i)
      (Fin.snoc (α := fun _ : Fin (2*n+1+1) => ℂ) (Y (Fin.init x)) (-1) j)
  have hbound (x : Fin (2*n+1+1) → E) (i j : Fin (2*n+1+1)) :
      ‖A x i j‖ ≤ k (x i) (x j)+1 := by
    cases i using Fin.lastCases with
    | last =>
      cases j using Fin.lastCases with
      | last =>
        dsimp [A, pairKernel]
        simp only [Fin.snoc_last, sub_self, zero_div, norm_zero]
        linarith [hk (x (Fin.last (2*n+1))) (x (Fin.last (2*n+1)))]
      | cast i =>
        dsimp only [A]
        rw [Fin.snoc_last, Fin.snoc_castSucc]
        have he : pairKernel (-1) (Y (Fin.init x) i) =
            -pairKernel (Y (Fin.init x) i) (-1) := by unfold pairKernel; ring
        rw [he, norm_neg]
        change ‖(Y (Fin.init x) i-(-1))/(1-Y (Fin.init x) i*(-1))‖ ≤ _
        rw [IsingBulk.HT.First.schur_ghost_entry (hg (Fin.init x) i), norm_one]
        linarith [hk (x (Fin.last (2*n+1))) (x i.castSucc)]
    | cast i =>
      cases j using Fin.lastCases with
      | last =>
        dsimp only [A]
        rw [Fin.snoc_castSucc, Fin.snoc_last]
        change ‖(Y (Fin.init x) i-(-1))/(1-Y (Fin.init x) i*(-1))‖ ≤ _
        rw [IsingBulk.HT.First.schur_ghost_entry (hg (Fin.init x) i), norm_one]
        linarith [hk (x i.castSucc) (x (Fin.last (2*n+1)))]
      | cast j =>
        dsimp only [A]
        rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
        exact (hA (Fin.init x) i j).trans (le_add_of_nonneg_right zero_le_one)
  have heq (x : Fin (2*n+1+1) → E) :
      labelPfaffian (A x) (n+1) (List.finRange (2*n+1+1)) =
        First.pairProduct (Y (Fin.init x)) :=
    (odd_pairProduct_eq_augmented n _ (hd (Fin.init x)) (hg (Fin.init x))).symm
  have hm : AEStronglyMeasurable (fun x : Fin (2*(n+1)) → E =>
      ((List.finRange (2*(n+1))).map (fun i => c (x i))).prod *
        ‖labelPfaffian (A x) (n+1) (List.finRange (2*(n+1)))‖)
      (Measure.pi (fun _ => μ)) := by
    change AEStronglyMeasurable (fun x : Fin (2*n+1+1) → E =>
      ((List.finRange (2*n+1+1)).map (fun i => c (x i))).prod *
        ‖labelPfaffian (A x) (n+1) (List.finRange (2*n+1+1))‖)
      (Measure.pi (fun _ => μ))
    simpa only [heq, ← List.ofFn_eq_map, List.prod_ofFn] using hmeas
  have hmain := integral_coupled_weighted_labelPfaffian_le (n+1) μ c hc A
    (fun x y => k x y+1) (fun x y => by linarith [hk x y]) hbound hpair hm
  have hint := integrable_coupled_weighted_labelPfaffian (n+1) μ c hc A
    (fun x y => k x y+1) (fun x y => by linarith [hk x y]) hbound hpair hm
  have hweight (x : Fin (2*n+1+1) → E) :
      ((List.finRange (2*(n+1))).map (fun i => c (x i))).prod *
        ‖labelPfaffian (A x) (n+1) (List.finRange (2*(n+1)))‖ =
      c (x (Fin.last (2*n+1))) *
        ((∏ i,c (Fin.init x i))*‖First.pairProduct (Y (Fin.init x))‖) := by
    change ((List.finRange (2*n+1+1)).map (fun i => c (x i))).prod *
        ‖labelPfaffian (A x) (n+1) (List.finRange (2*n+1+1))‖ = _
    rw [heq, ← List.ofFn_eq_map, List.prod_ofFn, Fin.prod_univ_castSucc]
    dsimp only [Fin.init]
    ring
  have hfun : (fun x : Fin (2*(n+1)) → E =>
      ((List.finRange (2*(n+1))).map (fun i => c (x i))).prod *
        ‖labelPfaffian (A x) (n+1) (List.finRange (2*(n+1)))‖) =
      (fun x : Fin (2*(n+1)) → E => c (x (Fin.last (2*n+1))) *
        ((∏ i,c (Fin.init x i))*‖First.pairProduct (Y (Fin.init x))‖)) := by
    funext x
    exact hweight x
  rw [hfun] at hmain hint
  refine ⟨integrable_of_dummy_last (2*n+1) μ c _ hint hmass.ne', ?_⟩
  change (∫ x : Fin (2*n+1+1) → E, c (x (Fin.last (2*n+1))) *
    ((∏ i,c (Fin.init x i))*‖First.pairProduct (Y (Fin.init x))‖)
      ∂Measure.pi (fun _ => μ)) ≤ _ at hmain
  rw [integral_dummy_last (2*n+1) μ c
    (fun x => (∏ i,c (x i))*‖First.pairProduct (Y x)‖)] at hmain
  apply (le_div_iff₀ hmass).mpr
  simpa only [mul_comm] using hmain

end
end IsingBulk.HT.Contour
