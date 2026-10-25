import IsingBulk.Joint.FormFactors.NormalSeries

/-! All mixed complex Fréchet derivatives of locally normally convergent
series. The bounds are derived by Cauchy estimates, not included as input. -/
namespace IsingBulk.Joint.FormFactors
noncomputable section
open Set Filter Metric
open scoped Topology

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]

theorem normalSeries_local_jet_bound (k : ℕ) {f : ℕ → E → G} {U : Set E}
    (hU : IsOpen U) (hf : ∀ i (j : ℕ) x, x ∈ U → ContDiffAt ℂ j (f i) x)
    {M : ℕ → ℝ} (hM : Summable M) (hb : ∀ i x, x ∈ U → ‖f i x‖ ≤ M i)
    {x : E} (hx : x ∈ U) :
    ∃ V ∈ 𝓝 x, IsOpen V ∧ V ⊆ U ∧ ∃ M' : ℕ → ℝ, Summable M' ∧
      ∀ i y, y ∈ V → ‖iteratedFDeriv ℂ k (f i) y‖ ≤ M' i := by
  induction k with
  | zero =>
    exact ⟨U,hU.mem_nhds hx,hU,Subset.rfl,M,hM,fun i y hy => by simpa using hb i y hy⟩
  | succ k ih =>
    obtain ⟨V,hVx,hV,hVU,M',hM',hb'⟩ := ih
    have hdiff : ∀ i, DifferentiableOn ℂ (iteratedFDeriv ℂ k (f i)) V := by
      intro i y hy
      exact ((hf i (1+k) y (hVU hy)).iteratedFDeriv_right (m := 1)
        (by simp)).differentiableAt_one.differentiableWithinAt
    obtain ⟨W,hWx,hW,_,hWV,M'',hM'',hb''⟩ :=
      normalSeries_local_derivative_bound hV hdiff hM' hb' (mem_of_mem_nhds hVx)
    exact ⟨W,hWx,hW,hWV.trans hVU,M'',hM'',fun i y hy => by
      simpa only [norm_fderiv_iteratedFDeriv] using hb'' i y hy⟩

theorem normalSeries_iteratedFDeriv_tsum (k : ℕ) {f : ℕ → E → G} {U : Set E}
    (hU : IsOpen U) (hf : ∀ i (j : ℕ) x, x ∈ U → ContDiffAt ℂ j (f i) x)
    {M : ℕ → ℝ} (hM : Summable M) (hb : ∀ i x, x ∈ U → ‖f i x‖ ≤ M i)
    {x : E} (hx : x ∈ U) :
    iteratedFDeriv ℂ k (fun y => ∑' i, f i y) x = ∑' i, iteratedFDeriv ℂ k (f i) x := by
  induction k generalizing x with
  | zero =>
    simp_rw [iteratedFDeriv_zero_eq_comp,Function.comp_apply]
    exact (continuousMultilinearCurryFin0 ℂ E G).symm.toContinuousLinearEquiv.map_tsum
  | succ k ih =>
    obtain ⟨V,hVx,hV,hVU,M',hM',hb'⟩ := normalSeries_local_jet_bound k hU hf hM hb hx
    have hdiff : ∀ i, DifferentiableOn ℂ (iteratedFDeriv ℂ k (f i)) V := by
      intro i y hy
      exact ((hf i (1+k) y (hVU hy)).iteratedFDeriv_right (m := 1)
        (by simp)).differentiableAt_one.differentiableWithinAt
    obtain ⟨W,hWx,hW,hWc,hWV,M'',hM'',hb''⟩ :=
      normalSeries_local_derivative_bound hV hdiff hM' hb' (mem_of_mem_nhds hVx)
    have hsum : Summable (fun i => iteratedFDeriv ℂ k (f i) x) :=
      .of_norm_bounded hM' (fun i => hb' i x (mem_of_mem_nhds hVx))
    have hd := hasFDerivAt_tsum_of_isPreconnected hM'' hW hWc
      (fun i y hy => (hdiff i |>.differentiableAt (hV.mem_nhds (hWV hy))).hasFDerivAt)
      hb'' (mem_of_mem_nhds hWx) hsum (mem_of_mem_nhds hWx)
    have he : iteratedFDeriv ℂ k (fun y => ∑' i, f i y) =ᶠ[𝓝 x]
        (fun y => ∑' i, iteratedFDeriv ℂ k (f i) y) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact ih hy
    simp_rw [iteratedFDeriv_succ_eq_comp_left,Function.comp_apply]
    rw [he.fderiv_eq,hd.fderiv]
    exact (continuousMultilinearCurryLeftEquiv ℂ
      (fun _ : Fin (k+1) => E) G).symm.toContinuousLinearEquiv.map_tsum

theorem normalSeries_iteratedFDeriv_hasSum (k : ℕ) {f : ℕ → E → G} {U : Set E}
    (hU : IsOpen U) (hf : ∀ i (j : ℕ) x, x ∈ U → ContDiffAt ℂ j (f i) x)
    {M : ℕ → ℝ} (hM : Summable M) (hb : ∀ i x, x ∈ U → ‖f i x‖ ≤ M i)
    {x : E} (hx : x ∈ U) :
    HasSum (fun i => iteratedFDeriv ℂ k (f i) x)
      (iteratedFDeriv ℂ k (fun y => ∑' i, f i y) x) := by
  obtain ⟨V,hVx,_,_,M',hM',hb'⟩ := normalSeries_local_jet_bound k hU hf hM hb hx
  have hs : Summable (fun i => iteratedFDeriv ℂ k (f i) x) :=
    .of_norm_bounded hM' (fun i => hb' i x (mem_of_mem_nhds hVx))
  rw [normalSeries_iteratedFDeriv_tsum k hU hf hM hb hx]
  exact hs.hasSum

end
end IsingBulk.Joint.FormFactors
