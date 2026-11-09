/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Closed annuli in normed groups

The closed annulus `{z | a ≤ ‖z - c‖ ∧ ‖z - c‖ ≤ b}` about `c` is compact in a proper space
(`Metric.isCompact_annulus`), and a point at positive distance from `c` is not `c`
(`Metric.ne_of_norm_sub_pos`).
-/

public section

open Metric Set

namespace Metric

/-- A point at positive distance from `c` is not `c`. -/
theorem ne_of_norm_sub_pos {E : Type*} [SeminormedAddCommGroup E] {c z : E}
    (hz : 0 < ‖z - c‖) : z ≠ c := by
  rintro rfl
  simp at hz

/-- A closed annulus is compact in a proper space. -/
theorem isCompact_annulus {E : Type*} [SeminormedAddCommGroup E] [ProperSpace E] (c : E)
    (a b : ℝ) : IsCompact {z : E | a ≤ ‖z - c‖ ∧ ‖z - c‖ ≤ b} :=
  (isCompact_closedBall c b).of_isClosed_subset
    ((isClosed_le continuous_const (continuous_id.sub continuous_const).norm).inter
      (isClosed_le (continuous_id.sub continuous_const).norm continuous_const))
    fun z hz ↦ by rw [mem_closedBall, dist_eq_norm]; exact hz.2

end Metric
