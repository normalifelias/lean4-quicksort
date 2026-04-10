-- import Lean4Quicksort.Legacy
import Lean4Quicksort.V1
import Lean4Quicksort.V2
import Lean4Quicksort.Benchmark

-- V1: Uses a list of tasks (ranges) left to sort.
-- V2: Uses half-stack recursion. Also uses Vectors during sorting.
-- Legacy: Splits array into list of tasks, being either left to sort or ready to be pushed. Deprecated.

def main : IO Unit := do
  benchmark 3 1000000 quicksort "V1"
  benchmark 3 1000000 quicksort2 "V2"
  benchmark 3 1000000 Array.qsort "qsort"
