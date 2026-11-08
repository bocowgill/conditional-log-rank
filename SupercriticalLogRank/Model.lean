module

/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

public import Mathlib

@[expose] public section

/-! The balanced exponential market and the variables used in the log-rank proof. -/

namespace SupercriticalLogRank

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators Topology

noncomputable section

abbrev Profile (n : ℕ) := (Bool × Fin n × Fin n) → ℝ

abbrev Vec (n : ℕ) := Fin n → ℝ

def marketMeasure (n : ℕ) : Measure (Profile n) :=
  Measure.pi fun _ ↦ expMeasure 1

def expVectorMeasure (n : ℕ) : Measure (Vec n) :=
  Measure.pi fun _ ↦ expMeasure 1

def stableEvent (n : ℕ) (ε : ℝ) : Set (Profile n) :=
  {p | ∀ i j : Fin n, i ≠ j →
    ¬ (p (false, i, i) + ε < p (false, i, j) ∧
      p (true, j, j) + ε < p (true, i, j))}

open scoped Classical in
def firmRankSum {n : ℕ} (p : Profile n) : ℕ :=
  ∑ i : Fin n, ∑ j : Fin n, if p (false, i, i) ≤ p (false, i, j) then 1 else 0

def rankCutoffEvent (n : ℕ) (t : ℝ) : Set (Profile n) :=
  {p | (firmRankSum p : ℝ) ≤ (n : ℝ) ^ (1 + t)}

def conditionalRankProbability (n : ℕ) (ε t : ℝ) : ℝ :=
  let μ := marketMeasure n
  μ.real (stableEvent n ε ∩ rankCutoffEvent n t) / μ.real (stableEvent n ε)

def conditionedMarket (n : ℕ) (ε : ℝ) : Measure (Profile n) :=
  ProbabilityTheory.cond (marketMeasure n) (stableEvent n ε)

def diagonalFirmScores {n : ℕ} (p : Profile n) : Vec n :=
  fun i ↦ Real.exp (-p (false, i, i))

def diagonalWorkerScores {n : ℕ} (p : Profile n) : Vec n :=
  fun i ↦ Real.exp (-p (true, i, i))

def scoreSum {n : ℕ} (x : Vec n) : ℝ :=
  ∑ i, x i

def cube (n : ℕ) : Set (Vec n) :=
  Set.pi Set.univ fun _ ↦ Set.Icc 0 1

def stabilityKernel {n : ℕ} (q : ℝ) (x y : Vec n) : ℝ :=
  ∏ i, ∏ j ∈ Finset.univ.erase i, (1 - q * x i * y j)

def simplexLaw (n : ℕ) : Measure (Vec n) :=
  Measure.map (fun e : Vec n ↦ fun i ↦ e i / scoreSum e) (expVectorMeasure n)

def columnIntegral {n : ℕ} (q s : ℝ) (u : Vec n) (j : Fin n) : ℝ :=
  ∫ z in (0 : ℝ)..(q * s), ∏ i ∈ Finset.univ.erase j, (1 - u i * z)

open scoped Classical in
def radialWeight (n : ℕ) (q s : ℝ) (u : Vec n) : ℝ :=
  if s • u ∈ cube n then ∏ j, columnIntegral q s u j else 0

def radialDensity (n : ℕ) (q s : ℝ) : ℝ :=
  ∫ u, radialWeight n q s u ∂simplexLaw n

end

end SupercriticalLogRank
