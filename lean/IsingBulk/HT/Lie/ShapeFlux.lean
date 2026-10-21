import IsingBulk.HT.Lie.CollisionWeights
import IsingBulk.Analysis.LieGeometry
import IsingBulk.Tail.AllBranchExteriorWeights

/-!
Actual relative-coordinate cube faces for the full-equality puncture.
The center coordinate is retained. The shape field has components Fi-Fq,
which is the vector transformation for xi=ui-uq; its boundary integral is
an actual signed sum of (N-2)-dimensional integrals. This module proves
surface measure and flux estimates rather than assuming their limits.
-/
namespace IsingBulk.HT.Lie
noncomputable section
open Set Filter MeasureTheory IsingBulk.Lie IsingBulk.Tail
open scoped Topology BigOperators

/-- Relative shape coordinates based at particle q. -/
def shapePoint {n : ℕ} (q : Fin (n+1)) (c : ℝ) (x : Fin n → ℝ) : Fin (n+1) → ℝ :=
  q.insertNth c (fun i => c+x i)

@[simp] theorem shapePoint_center {n : ℕ} (q : Fin (n+1)) (c : ℝ) (x : Fin n → ℝ) :
    shapePoint q c x q = c := Fin.insertNth_apply_same _ _ _

@[simp] theorem shapePoint_relative {n : ℕ} (q : Fin (n+1)) (c : ℝ)
    (x : Fin n → ℝ) (i : Fin n) :
    shapePoint q c x (q.succAbove i)-shapePoint q c x q = x i := by
  simp [shapePoint]

/-- The center coordinate remains visible in the physical support bound. -/
theorem shapePoint_coordinate_bound {n : ℕ} (q : Fin (n+1)) (c : ℝ)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (x : Fin n → ℝ)
    (hx : x ∈ Icc (fun _ => -ρ) (fun _ => ρ)) (i : Fin (n+1)) :
    |shapePoint q c x i| ≤ |c|+ρ := by
  rcases Fin.eq_self_or_eq_succAbove q i with rfl | ⟨l,rfl⟩
  · simp only [shapePoint_center]
    linarith
  · simpa [shapePoint] using (abs_add_le c (x l)).trans
      (show |c|+|x l|≤|c|+ρ by linarith [abs_le.mpr ⟨hx.1 l,hx.2 l⟩])

/-- Each retained shape face has its literal transverse cube parameter. -/
def cubeFacePoint {n : ℕ} (i : Fin (n+1)) (upper : Bool) (ρ : ℝ)
    (y : Fin n → ℝ) : Fin (n+1) → ℝ :=
  i.insertNth (if upper then ρ else -ρ) y

theorem cubeFacePoint_mem {n : ℕ} (i : Fin (n+1)) (upper : Bool)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (y : Fin n → ℝ)
    (hy : y ∈ Icc (fun _ => -ρ) (fun _ => ρ)) :
    cubeFacePoint i upper ρ y ∈ Icc (fun _ => -ρ) (fun _ => ρ) := by
  have hh : ∀ l, -ρ ≤ cubeFacePoint i upper ρ y l ∧
      cubeFacePoint i upper ρ y l ≤ ρ := by
    intro l
    rcases Fin.eq_self_or_eq_succAbove i l with rfl | ⟨k,rfl⟩
    · cases upper <;> simp [cubeFacePoint] <;> linarith
    · simpa [cubeFacePoint] using And.intro (hy.1 k) (hy.2 k)
  exact ⟨fun l => (hh l).1,fun l => (hh l).2⟩

/-- A shape face is separated from full equality by its own radius. -/
theorem shape_face_diameter_lower {n : ℕ} (q : Fin (n+2)) (c : ℝ)
    (i : Fin (n+1)) (upper : Bool) {ρ : ℝ} (hρ : 0 ≤ ρ) (y : Fin n → ℝ) :
    ρ ≤ allBranchExteriorDiameter (shapePoint q c (cubeFacePoint i upper ρ y)) := by
  have hh := allBranchExterior_pair_le_diameter
    (shapePoint q c (cubeFacePoint i upper ρ y)) (q.succAbove i) q
  rw [shapePoint_relative] at hh
  cases upper <;> simpa [cubeFacePoint,abs_of_nonneg hρ] using hh

/-- The shape cube has diameter at most twice its radius. -/
theorem shape_point_diameter_upper {n : ℕ} (q : Fin (n+1)) (c : ℝ)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (x : Fin n → ℝ)
    (hx : x ∈ Icc (fun _ => -ρ) (fun _ => ρ)) :
    allBranchExteriorDiameter (shapePoint q c x) ≤ 2*ρ := by
  have habs : ∀ i, |shapePoint q c x i-c| ≤ ρ := by
    intro i
    rcases Fin.eq_self_or_eq_succAbove q i with rfl | ⟨k,rfl⟩
    · simpa using hρ
    · simpa [shapePoint] using abs_le.mpr ⟨hx.1 k,hx.2 k⟩
  change (allBranchExteriorDiameterNN (shapePoint q c x):ℝ) ≤ 2*ρ
  have hnonneg : 0 ≤ 2*ρ := by positivity
  change allBranchExteriorDiameterNN (shapePoint q c x) ≤ ⟨2*ρ,hnonneg⟩
  apply Finset.sup_le
  intro a _
  change |shapePoint q c x a.1-shapePoint q c x a.2| ≤ 2*ρ
  calc
    _ = |(shapePoint q c x a.1-c)-(shapePoint q c x a.2-c)| := by congr 1; ring
    _ ≤ |shapePoint q c x a.1-c|+|shapePoint q c x a.2-c| := by
      simpa only [Real.norm_eq_abs] using norm_sub_le
        (shapePoint q c x a.1-c) (shapePoint q c x a.2-c)
    _ ≤ 2*ρ := by linarith [habs a.1,habs a.2]

theorem cube_transverse_volume (n : ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    volume.real (Icc (fun _ : Fin n => -ρ) (fun _ => ρ)) = (2*ρ)^n := by
  change (volume (Icc (fun _ : Fin n => -ρ) (fun _ => ρ))).toReal = _
  rw [Real.volume_Icc_pi_toReal (fun _ => by linarith)]
  simp [sub_neg_eq_add,← two_mul]

/-- A direct estimate of the actual signed rectangular face sum. -/
theorem cube_boundaryFlux_norm_le {n : ℕ} (F : AngularSpace n → Fin (n+1) → ℂ)
    {ρ B : ℝ} (hρ : 0 ≤ ρ)
    (hF : ∀ i upper y, y ∈ Icc (fun _ => -ρ) (fun _ => ρ) →
      ‖F (cubeFacePoint i upper ρ y) i‖ ≤ B) :
    ‖boundaryFlux (fun _ => -ρ) (fun _ => ρ) F‖ ≤
      2*(n+1:ℝ)*B*(2*ρ)^n := by
  have hface (i : Fin (n+1)) (upper : Bool) :
      ‖∫ y in Icc (fun _ : Fin n => -ρ) (fun _ => ρ),
        F (cubeFacePoint i upper ρ y) i‖ ≤ B*(2*ρ)^n := by
    have hh := norm_setIntegral_le_of_norm_le_const
      (μ := volume) isCompact_Icc.measure_lt_top (hF i upper)
    simpa only [cube_transverse_volume n hρ] using hh
  unfold boundaryFlux
  calc
    _ ≤ ∑ i : Fin (n+1), ‖(∫ y in Icc (fun _ : Fin n => -ρ) (fun _ => ρ),
        F (i.insertNth ρ y) i) -
      ∫ y in Icc (fun _ : Fin n => -ρ) (fun _ => ρ), F (i.insertNth (-ρ) y) i‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _i : Fin (n+1), 2*B*(2*ρ)^n := by
      apply Finset.sum_le_sum
      intro i _
      have hh := norm_sub_le
        (∫ y in Icc (fun _ : Fin n => -ρ) (fun _ => ρ), F (i.insertNth ρ y) i)
        (∫ y in Icc (fun _ : Fin n => -ρ) (fun _ => ρ), F (i.insertNth (-ρ) y) i)
      have hp := hface i true
      have hm := hface i false
      simp only [cubeFacePoint,ite_true,Bool.false_eq_true,ite_false] at hp hm
      linarith
    _ = _ := by simp; ring

/-- Relative-coordinate flux, retaining all physical vector components. -/
def shapeCubeFlux {n : ℕ} (q : Fin (n+2)) (c ρ : ℝ)
    (F : (Fin (n+2) → ℝ) → Fin (n+2) → ℂ) : ℂ :=
  boundaryFlux (fun _ => -ρ) (fun _ => ρ)
    (fun x i => F (shapePoint q c x) (q.succAbove i)-F (shapePoint q c x) q)

/-- The geometric (N-2)-dimensional measure is paid exactly once. -/
theorem shapeCubeFlux_norm_le {n : ℕ} (q : Fin (n+2)) (c : ℝ)
    (F : (Fin (n+2) → ℝ) → Fin (n+2) → ℂ) (C : ℝ) (P : ℕ)
    {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hF : ∀ i upper y, y ∈ Icc (fun _ => -ρ) (fun _ => ρ) → ∀ l,
      ‖F (shapePoint q c (cubeFacePoint i upper ρ y)) l‖ ≤ C*ρ^P) :
    ‖shapeCubeFlux q c ρ F‖ ≤ (4*(n+1:ℝ)*C*2^n)*ρ^(P+n) := by
  have hh := cube_boundaryFlux_norm_le
    (fun x i => F (shapePoint q c x) (q.succAbove i)-F (shapePoint q c x) q) hρ
    (B := 2*C*ρ^P) (by
      intro i upper y hy
      have ht := norm_sub_le
        (F (shapePoint q c (cubeFacePoint i upper ρ y)) (q.succAbove i))
        (F (shapePoint q c (cubeFacePoint i upper ρ y)) q)
      linarith [hF i upper y hy (q.succAbove i),hF i upper y hy q])
  change ‖shapeCubeFlux q c ρ F‖ ≤ _ at hh
  apply hh.trans_eq
  rw [mul_pow,pow_add]
  ring

/-- The literal face sum tends to zero from its local field bound. -/
theorem shapeCubeFlux_tendsto_zero {n : ℕ} (q : Fin (n+2)) (c : ℝ)
    (F : (Fin (n+2) → ℝ) → Fin (n+2) → ℂ) (C : ℝ) (P : ℕ)
    (hP : 0 < P+n)
    (hF : ∀ᶠ ρ in 𝓝[>] (0:ℝ), ∀ i upper y,
      y ∈ Icc (fun _ => -ρ) (fun _ => ρ) → ∀ l,
      ‖F (shapePoint q c (cubeFacePoint i upper ρ y)) l‖ ≤ C*ρ^P) :
    Tendsto (fun ρ => shapeCubeFlux q c ρ F) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  apply flux_tendsto_zero_of_power_bound _ (fun ρ => ρ)
    (4*(n+1:ℝ)*C*2^n) (P+n) hP continuousWithinAt_id
  filter_upwards [hF,self_mem_nhdsWithin] with ρ hρ hpos
  exact shapeCubeFlux_norm_le q c F C P hpos.le hρ

end
end IsingBulk.HT.Lie
