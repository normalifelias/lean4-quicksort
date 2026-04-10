# lean4-quicksort

**(Lean4Quicksort.)V_.quicksort_**  
Sorts a comparable array of any type efficiently by splitting it along a selected pivot. See version details below.

Usage: quicksort [array]

**(Lean4Quicksort.)Benchmark.benchmark**  
Runs a number of tests on a number of shuffled Nats with a selected algorithm, returns runtimes.  

Usage: benchmark [number of tests] [number of elements] [target sorting algorithm]  
  
**Notes**  
  
- V1: Uses a list of tasks (ranges) left to sort.
- V2: Uses half-stack recursion. Also uses Vectors during sorting.
- Legacy: Splits array into list of tasks, being either left to sort or ready to be pushed. Deprecated.


**TODO:**
- no more sorry
- insertion sort
- permutation + pairwise (from the bottom up) (additional requirements for Ord => LE a, Ord a, Std.LawfulOrderOrd a, Std.IsLinearPreorder a; maybe also LT)
- stylistic enhancements
- setup development

