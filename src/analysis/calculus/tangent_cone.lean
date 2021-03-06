/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import analysis.convex.basic analysis.normed_space.bounded_linear_maps analysis.specific_limits

/-!
# Tangent cone

In this file, we define two predicates `unique_diff_within_at 𝕜 s x` and `unique_diff_on 𝕜 s`
ensuring that, if a function has two derivatives, then they have to coincide. As a direct
definition of this fact (quantifying on all target types and all functions) would depend on
universes, we use a more intrinsic definition: if all the possible tangent directions to the set
`s` at the point `x` span a dense subset of the whole subset, it is easy to check that the
derivative has to be unique.

Therefore, we introduce the set of all tangent directions, named `tangent_cone_at`,
and express `unique_diff_within_at` and `unique_diff_on` in terms of it.
One should however think of this definition as an implementation detail: the only reason to
introduce the predicates `unique_diff_within_at` and `unique_diff_on` is to ensure the uniqueness
of the derivative. This is why their names reflect their uses, and not how they are defined.

## Implementation details

Note that this file is imported by `fderiv.lean`. Hence, derivatives are not defined yet. The
property of uniqueness of the derivative is therefore proved in `fderiv.lean`, but based on the
properties of the tangent cone we prove here.
-/

variables (𝕜 : Type*) [nondiscrete_normed_field 𝕜]
variables {E : Type*} [normed_group E] [normed_space 𝕜 E]
variables {F : Type*} [normed_group F] [normed_space 𝕜 F]
variables {G : Type*} [normed_group G] [normed_space ℝ G]

set_option class.instance_max_depth 50
open filter set
open_locale topological_space

/-- The set of all tangent directions to the set `s` at the point `x`. -/
def tangent_cone_at (s : set E) (x : E) : set E :=
{y : E | ∃(c : ℕ → 𝕜) (d : ℕ → E), (∀ᶠ n in at_top, x + d n ∈ s) ∧
  (tendsto (λn, ∥c n∥) at_top at_top) ∧ (tendsto (λn, c n • d n) at_top (𝓝 y))}

/-- A property ensuring that the tangent cone to `s` at `x` spans a dense subset of the whole space.
The main role of this property is to ensure that the differential within `s` at `x` is unique,
hence this name. The uniqueness it asserts is proved in `unique_diff_within_at.eq` in `fderiv.lean`.
To avoid pathologies in dimension 0, we also require that `x` belongs to the closure of `s` (which
is automatic when `E` is not `0`-dimensional).
 -/
def unique_diff_within_at (s : set E) (x : E) : Prop :=
closure ((submodule.span 𝕜 (tangent_cone_at 𝕜 s x)) : set E) = univ ∧ x ∈ closure s

/-- A property ensuring that the tangent cone to `s` at any of its points spans a dense subset of
the whole space.  The main role of this property is to ensure that the differential along `s` is
unique, hence this name. The uniqueness it asserts is proved in `unique_diff_on.eq` in
`fderiv.lean`. -/
def unique_diff_on (s : set E) : Prop :=
∀x ∈ s, unique_diff_within_at 𝕜 s x

variables {𝕜} {x y : E} {s t : set E}

section tangent_cone
/- This section is devoted to the properties of the tangent cone. -/

open normed_field

lemma tangent_cone_univ : tangent_cone_at 𝕜 univ x = univ :=
begin
  refine univ_subset_iff.1 (λy hy, _),
  rcases exists_one_lt_norm 𝕜 with ⟨w, hw⟩,
  refine ⟨λn, w^n, λn, (w^n)⁻¹ • y, univ_mem_sets' (λn, mem_univ _),  _, _⟩,
  { simp only [norm_pow],
    exact tendsto_pow_at_top_at_top_of_gt_1 hw },
  { convert tendsto_const_nhds,
    ext n,
    have : w ^ n * (w ^ n)⁻¹ = 1,
    { apply mul_inv_cancel,
      apply pow_ne_zero,
      simpa [norm_eq_zero] using (ne_of_lt (lt_trans zero_lt_one hw)).symm },
    rw [smul_smul, this, one_smul] }
end

lemma tangent_cone_mono (h : s ⊆ t) :
  tangent_cone_at 𝕜 s x ⊆ tangent_cone_at 𝕜 t x :=
begin
  rintros y ⟨c, d, ds, ctop, clim⟩,
  exact ⟨c, d, mem_sets_of_superset ds (λn hn, h hn), ctop, clim⟩
end

/-- Auxiliary lemma ensuring that, under the assumptions defining the tangent cone,
the sequence `d` tends to 0 at infinity. -/
lemma tangent_cone_at.lim_zero {α : Type*} (l : filter α) {c : α → 𝕜} {d : α → E}
  (hc : tendsto (λn, ∥c n∥) l at_top) (hd : tendsto (λn, c n • d n) l (𝓝 y)) :
  tendsto d l (𝓝 0) :=
begin
  have A : tendsto (λn, ∥c n∥⁻¹) l (𝓝 0) := tendsto_inv_at_top_zero.comp hc,
  have B : tendsto (λn, ∥c n • d n∥) l (𝓝 ∥y∥) :=
    (continuous_norm.tendsto _).comp hd,
  have C : tendsto (λn, ∥c n∥⁻¹ * ∥c n • d n∥) l (𝓝 (0 * ∥y∥)) := A.mul B,
  rw zero_mul at C,
  have : ∀ᶠ n in l, ∥c n∥⁻¹ * ∥c n • d n∥ = ∥d n∥,
  { apply mem_sets_of_superset (ne_mem_of_tendsto_norm_at_top hc 0) (λn hn, _),
    rw [mem_set_of_eq, norm_smul, ← mul_assoc, inv_mul_cancel, one_mul],
    rwa [ne.def, norm_eq_zero] },
  have D : tendsto (λ n, ∥d n∥) l (𝓝 0) :=
    tendsto.congr' this C,
  rw tendsto_zero_iff_norm_tendsto_zero,
  exact D
end

lemma tangent_cone_mono_nhds (h : nhds_within x s ≤ nhds_within x t) :
  tangent_cone_at 𝕜 s x ⊆ tangent_cone_at 𝕜 t x :=
begin
  rintros y ⟨c, d, ds, ctop, clim⟩,
  refine ⟨c, d, _, ctop, clim⟩,
  suffices : tendsto (λ n, x + d n) at_top (nhds_within x t),
    from tendsto_principal.1 (tendsto_inf.1 this).2,
  apply tendsto_le_right h,
  refine tendsto_inf.2 ⟨_, tendsto_principal.2 ds⟩,
  simpa only [add_zero] using tendsto_const_nhds.add (tangent_cone_at.lim_zero at_top ctop clim)
end

/-- Tangent cone of `s` at `x` depends only on `nhds_within x s`. -/
lemma tangent_cone_congr (h : nhds_within x s = nhds_within x t) :
  tangent_cone_at 𝕜 s x = tangent_cone_at 𝕜 t x :=
subset.antisymm
  (tangent_cone_mono_nhds $ le_of_eq h)
  (tangent_cone_mono_nhds $ le_of_eq h.symm)

/-- Intersecting with a neighborhood of the point does not change the tangent cone. -/
lemma tangent_cone_inter_nhds (ht : t ∈ 𝓝 x) :
  tangent_cone_at 𝕜 (s ∩ t) x = tangent_cone_at 𝕜 s x :=
tangent_cone_congr (nhds_within_restrict' _ ht).symm

/-- The tangent cone of a product contains the tangent cone of its left factor. -/
lemma subset_tangent_cone_prod_left {t : set F} {y : F} (ht : y ∈ closure t) :
  set.prod (tangent_cone_at 𝕜 s x) {(0 : F)} ⊆ tangent_cone_at 𝕜 (set.prod s t) (x, y) :=
begin
  rintros ⟨v, w⟩ ⟨⟨c, d, hd, hc, hy⟩, hw⟩,
  have : w = 0, by simpa using hw,
  rw this,
  have : ∀n, ∃d', y + d' ∈ t ∧ ∥c n • d'∥ ≤ ((1:ℝ)/2)^n,
  { assume n,
    have c_pos : 0 < 1 + ∥c n∥ :=
      add_pos_of_pos_of_nonneg zero_lt_one (norm_nonneg _),
    rcases metric.mem_closure_iff'.1 ht ((1 + ∥c n∥)⁻¹ * (1/2)^n) _ with ⟨z, z_pos, hz⟩,
    refine ⟨z - y, _, _⟩,
    { convert z_pos, abel },
    { rw [norm_smul, ← dist_eq_norm, dist_comm],
      calc ∥c n∥ * dist y z ≤ (1 + ∥c n∥) * ((1 + ∥c n∥)⁻¹ * (1/2)^n) :
      begin
        apply mul_le_mul _ (le_of_lt hz) dist_nonneg (le_of_lt c_pos),
        simp only [zero_le_one, le_add_iff_nonneg_left]
      end
      ... = (1/2)^n :
      begin
        rw [← mul_assoc, mul_inv_cancel, one_mul],
        exact ne_of_gt c_pos
      end },
    { apply mul_pos (inv_pos c_pos) (pow_pos _ _),
      norm_num } },
  choose d' hd' using this,
  refine ⟨c, λn, (d n, d' n), _, hc, _⟩,
  show ∀ᶠ n in at_top, (x, y) + (d n, d' n) ∈ set.prod s t,
  { apply filter.mem_sets_of_superset hd,
    assume n hn,
    simp at hn,
    simp [hn, (hd' n).1] },
  { apply tendsto_prod_mk_nhds hy,
    change tendsto (λ (n : ℕ), c n • d' n) at_top (𝓝 0),
    rw tendsto_zero_iff_norm_tendsto_zero,
    refine squeeze_zero (λn, norm_nonneg _) (λn, (hd' n).2) _,
    apply tendsto_pow_at_top_nhds_0_of_lt_1; norm_num }
end

/-- The tangent cone of a product contains the tangent cone of its right factor. -/
lemma subset_tangent_cone_prod_right {t : set F} {y : F}
  (hs : x ∈ closure s) :
  set.prod {(0 : E)} (tangent_cone_at 𝕜 t y) ⊆ tangent_cone_at 𝕜 (set.prod s t) (x, y) :=
begin
  rintros ⟨v, w⟩ ⟨hv, ⟨c, d, hd, hc, hy⟩⟩,
  have : v = 0, by simpa using hv,
  rw this,
  have : ∀n, ∃d', x + d' ∈ s ∧ ∥c n • d'∥ ≤ ((1:ℝ)/2)^n,
  { assume n,
    have c_pos : 0 < 1 + ∥c n∥ :=
      add_pos_of_pos_of_nonneg zero_lt_one (norm_nonneg _),
    rcases metric.mem_closure_iff'.1 hs ((1 + ∥c n∥)⁻¹ * (1/2)^n) _ with ⟨z, z_pos, hz⟩,
    refine ⟨z - x, _, _⟩,
    { convert z_pos, abel },
    { rw [norm_smul, ← dist_eq_norm, dist_comm],
      calc ∥c n∥ * dist x z ≤ (1 + ∥c n∥) * ((1 + ∥c n∥)⁻¹ * (1/2)^n) :
      begin
        apply mul_le_mul _ (le_of_lt hz) dist_nonneg (le_of_lt c_pos),
        simp only [zero_le_one, le_add_iff_nonneg_left]
      end
      ... = (1/2)^n :
      begin
        rw [← mul_assoc, mul_inv_cancel, one_mul],
        exact ne_of_gt c_pos
      end },
    { apply mul_pos (inv_pos c_pos) (pow_pos _ _),
      norm_num } },
  choose d' hd' using this,
  refine ⟨c, λn, (d' n, d n), _, hc, _⟩,
  show ∀ᶠ n in at_top, (x, y) + (d' n, d n) ∈ set.prod s t,
  { apply filter.mem_sets_of_superset hd,
    assume n hn,
    simp at hn,
    simp [hn, (hd' n).1] },
  { apply tendsto_prod_mk_nhds _ hy,
    change tendsto (λ (n : ℕ), c n • d' n) at_top (𝓝 0),
    rw tendsto_zero_iff_norm_tendsto_zero,
    refine squeeze_zero (λn, norm_nonneg _) (λn, (hd' n).2) _,
    apply tendsto_pow_at_top_nhds_0_of_lt_1; norm_num }
end

/-- If a subset of a real vector space contains a segment, then the direction of this
segment belongs to the tangent cone at its endpoints. -/
lemma mem_tangent_cone_of_segment_subset {s : set G} {x y : G} (h : segment x y ⊆ s) :
  y - x ∈ tangent_cone_at ℝ s x :=
begin
  let w : ℝ := 2,
  let c := λn:ℕ, (2:ℝ)^n,
  let d := λn:ℕ, (c n)⁻¹ • (y-x),
  refine ⟨c, d, filter.univ_mem_sets' (λn, h _), _, _⟩,
  show x + d n ∈ segment x y,
  { rw segment_eq_image,
    refine ⟨(c n)⁻¹, ⟨_, _⟩, _⟩,
    { rw inv_nonneg, apply pow_nonneg, norm_num },
    { apply inv_le_one, apply one_le_pow_of_one_le, norm_num },
    { simp only [d, sub_smul, smul_sub, one_smul], abel } },
  show filter.tendsto (λ (n : ℕ), ∥c n∥) filter.at_top filter.at_top,
  { have : (λ (n : ℕ), ∥c n∥) = c,
      by { ext n, exact abs_of_nonneg (pow_nonneg (by norm_num) _) },
    rw this,
    exact tendsto_pow_at_top_at_top_of_gt_1 (by norm_num) },
  show filter.tendsto (λ (n : ℕ), c n • d n) filter.at_top (𝓝 (y - x)),
  { have : (λ (n : ℕ), c n • d n) = (λn, y - x),
    { ext n,
      simp only [d, smul_smul],
      rw [mul_inv_cancel, one_smul],
      exact pow_ne_zero _ (by norm_num) },
    rw this,
    apply tendsto_const_nhds }
end

end tangent_cone

section unique_diff
/- This section is devoted to properties of the predicates `unique_diff_within_at` and
`unique_diff_on`. -/

lemma unique_diff_within_at_univ : unique_diff_within_at 𝕜 univ x :=
by { rw [unique_diff_within_at, tangent_cone_univ], simp }

lemma unique_diff_on_univ : unique_diff_on 𝕜 (univ : set E) :=
λx hx, unique_diff_within_at_univ

lemma unique_diff_within_at.mono_nhds (h : unique_diff_within_at 𝕜 s x)
  (st : nhds_within x s ≤ nhds_within x t) :
  unique_diff_within_at 𝕜 t x :=
begin
  unfold unique_diff_within_at at *,
  rw [← univ_subset_iff, ← h.1],
  rw [mem_closure_iff_nhds_within_ne_bot] at h ⊢,
  exact ⟨closure_mono (submodule.span_mono (tangent_cone_mono_nhds st)),
    lattice.ne_bot_of_le_ne_bot h.2 st⟩
end

lemma unique_diff_within_at.mono (h : unique_diff_within_at 𝕜 s x) (st : s ⊆ t) :
  unique_diff_within_at 𝕜 t x :=
h.mono_nhds $ nhds_within_mono _ st

lemma unique_diff_within_at_congr (st : nhds_within x s = nhds_within x t) :
  unique_diff_within_at 𝕜 s x ↔ unique_diff_within_at 𝕜 t x :=
⟨λ h, h.mono_nhds $ le_of_eq st, λ h, h.mono_nhds $ le_of_eq st.symm⟩

lemma unique_diff_within_at_inter (ht : t ∈ 𝓝 x) :
  unique_diff_within_at 𝕜 (s ∩ t) x ↔ unique_diff_within_at 𝕜 s x :=
unique_diff_within_at_congr $ (nhds_within_restrict' _ ht).symm

lemma unique_diff_within_at.inter (hs : unique_diff_within_at 𝕜 s x) (ht : t ∈ 𝓝 x) :
  unique_diff_within_at 𝕜 (s ∩ t) x :=
(unique_diff_within_at_inter ht).2 hs

lemma unique_diff_within_at_inter' (ht : t ∈ nhds_within x s) :
  unique_diff_within_at 𝕜 (s ∩ t) x ↔ unique_diff_within_at 𝕜 s x :=
unique_diff_within_at_congr $ (nhds_within_restrict'' _ ht).symm

lemma unique_diff_within_at.inter' (hs : unique_diff_within_at 𝕜 s x) (ht : t ∈ nhds_within x s) :
  unique_diff_within_at 𝕜 (s ∩ t) x :=
(unique_diff_within_at_inter' ht).2 hs

lemma is_open.unique_diff_within_at (hs : is_open s) (xs : x ∈ s) : unique_diff_within_at 𝕜 s x :=
begin
  have := unique_diff_within_at_univ.inter (mem_nhds_sets hs xs),
  rwa univ_inter at this
end

lemma unique_diff_on.inter (hs : unique_diff_on 𝕜 s) (ht : is_open t) : unique_diff_on 𝕜 (s ∩ t) :=
λx hx, (hs x hx.1).inter (mem_nhds_sets ht hx.2)

lemma is_open.unique_diff_on (hs : is_open s) : unique_diff_on 𝕜 s :=
λx hx, is_open.unique_diff_within_at hs hx

/-- The product of two sets of unique differentiability at points `x` and `y` has unique
differentiability at `(x, y)`. -/
lemma unique_diff_within_at.prod {t : set F} {y : F}
  (hs : unique_diff_within_at 𝕜 s x) (ht : unique_diff_within_at 𝕜 t y) :
  unique_diff_within_at 𝕜 (set.prod s t) (x, y) :=
begin
  rw [unique_diff_within_at, ← univ_subset_iff] at ⊢ hs ht,
  split,
  { assume v _,
    rw metric.mem_closure_iff',
    assume ε ε_pos,
    rcases v with ⟨v₁, v₂⟩,
    rcases metric.mem_closure_iff'.1 (hs.1 (mem_univ v₁)) ε ε_pos with ⟨w₁, w₁_mem, h₁⟩,
    rcases metric.mem_closure_iff'.1 (ht.1 (mem_univ v₂)) ε ε_pos with ⟨w₂, w₂_mem, h₂⟩,
    have I₁ : (w₁, (0 : F)) ∈ submodule.span 𝕜 (tangent_cone_at 𝕜 (set.prod s t) (x, y)),
    { apply submodule.span_induction w₁_mem,
      { assume w hw,
        have : (w, (0 : F)) ∈ (set.prod (tangent_cone_at 𝕜 s x) {(0 : F)}),
        { rw mem_prod,
          simp [hw],
          apply mem_insert },
        have : (w, (0 : F)) ∈ tangent_cone_at 𝕜 (set.prod s t) (x, y) :=
          subset_tangent_cone_prod_left ht.2 this,
        exact submodule.subset_span this },
      { exact submodule.zero_mem _ },
      { assume a b ha hb,
        have : (a, (0 : F)) + (b, (0 : F)) = (a + b, (0 : F)), by simp,
        rw ← this,
        exact submodule.add_mem _ ha hb },
      { assume c a ha,
        have : c • (0 : F) = (0 : F), by simp,
        rw ← this,
        exact submodule.smul_mem _ _ ha } },
    have I₂ : ((0 : E), w₂) ∈ submodule.span 𝕜 (tangent_cone_at 𝕜 (set.prod s t) (x, y)),
    { apply submodule.span_induction w₂_mem,
      { assume w hw,
        have : ((0 : E), w) ∈ (set.prod {(0 : E)} (tangent_cone_at 𝕜 t y)),
        { rw mem_prod,
          simp [hw],
          apply mem_insert },
        have : ((0 : E), w) ∈ tangent_cone_at 𝕜 (set.prod s t) (x, y) :=
          subset_tangent_cone_prod_right hs.2 this,
        exact submodule.subset_span this },
      { exact submodule.zero_mem _ },
      { assume a b ha hb,
        have : ((0 : E), a) + ((0 : E), b) = ((0 : E), a + b), by simp,
        rw ← this,
        exact submodule.add_mem _ ha hb },
      { assume c a ha,
        have : c • (0 : E) = (0 : E), by simp,
        rw ← this,
        exact submodule.smul_mem _ _ ha } },
    have I : (w₁, w₂) ∈ submodule.span 𝕜 (tangent_cone_at 𝕜 (set.prod s t) (x, y)),
    { have : (w₁, (0 : F)) + ((0 : E), w₂) = (w₁, w₂), by simp,
      rw ← this,
      exact submodule.add_mem _ I₁ I₂ },
    refine ⟨(w₁, w₂), I, _⟩,
    simp [dist, h₁, h₂] },
  { simp [closure_prod_eq, mem_prod_iff, hs.2, ht.2] }
end

/-- The product of two sets of unique differentiability is a set of unique differentiability. -/
lemma unique_diff_on.prod {t : set F} (hs : unique_diff_on 𝕜 s) (ht : unique_diff_on 𝕜 t) :
  unique_diff_on 𝕜 (set.prod s t) :=
λ ⟨x, y⟩ h, unique_diff_within_at.prod (hs x h.1) (ht y h.2)

/-- In a real vector space, a convex set with nonempty interior is a set of unique
differentiability. -/
theorem unique_diff_on_convex {s : set G} (conv : convex s) (hs : (interior s).nonempty) :
  unique_diff_on ℝ s :=
begin
  assume x xs,
  have A : ∀v, ∃a∈ tangent_cone_at ℝ s x, ∃b∈ tangent_cone_at ℝ s x, ∃δ>(0:ℝ), δ • v = b-a,
  { assume v,
    rcases hs with ⟨y, hy⟩,
    have ys : y ∈ s := interior_subset hy,
    have : ∃(δ : ℝ), 0<δ ∧ y + δ • v ∈ s,
    { by_cases h : ∥v∥ = 0,
      { exact ⟨1, zero_lt_one, by simp [(norm_eq_zero _).1 h, ys]⟩ },
      { rcases mem_interior.1 hy with ⟨u, us, u_open, yu⟩,
        rcases metric.is_open_iff.1 u_open y yu with ⟨ε, εpos, hε⟩,
        let δ := (ε/2) / ∥v∥,
        have δpos : 0 < δ := div_pos (half_pos εpos) (lt_of_le_of_ne (norm_nonneg _) (ne.symm h)),
        have : y + δ • v ∈ s,
        { apply us (hε _),
          rw [metric.mem_ball, dist_eq_norm],
          calc ∥(y + δ • v) - y ∥ = ∥δ • v∥ : by {congr' 1, abel }
          ... = ∥δ∥ * ∥v∥ : norm_smul _ _
          ... = δ * ∥v∥ : by simp only [norm, abs_of_nonneg (le_of_lt δpos)]
          ... = ε /2 : div_mul_cancel _ h
          ... < ε : half_lt_self εpos },
        exact ⟨δ, δpos, this⟩ } },
    rcases this with ⟨δ, δpos, hδ⟩,
    refine ⟨y-x, _, (y + δ • v) - x, _, δ, δpos, by abel⟩,
    exact mem_tangent_cone_of_segment_subset (conv.segment_subset xs ys),
    exact mem_tangent_cone_of_segment_subset (conv.segment_subset xs hδ) },
  have B : ∀v:G, v ∈ submodule.span ℝ (tangent_cone_at ℝ s x),
  { assume v,
    rcases A v with ⟨a, ha, b, hb, δ, hδ, h⟩,
    have : v = δ⁻¹ • (b - a),
      by { rw [← h, smul_smul, inv_mul_cancel, one_smul], exact (ne_of_gt hδ) },
    rw this,
    exact submodule.smul_mem _ _
      (submodule.sub_mem _ (submodule.subset_span hb) (submodule.subset_span ha)) },
  refine ⟨univ_subset_iff.1 (λv hv, subset_closure (B v)), subset_closure xs⟩
end

/-- The real interval `[0, 1]` is a set of unique differentiability. -/
lemma unique_diff_on_Icc_zero_one : unique_diff_on ℝ (Icc (0:ℝ) 1) :=
begin
  apply unique_diff_on_convex (convex_Icc 0 1),
  have : (1/(2:ℝ)) ∈ interior (Icc (0:ℝ) 1) :=
    mem_interior.2 ⟨Ioo (0:ℝ) 1, Ioo_subset_Icc_self, is_open_Ioo, by norm_num, by norm_num⟩,
  exact ⟨_, this⟩
end

end unique_diff
