# lean4-quicksort

**(Lean4Quicksort.)Benchmark.benchmark**  
Runs a number of tests on a number of shuffled Nats with a selected algorithm, returns runtimes  
Usage: benchmark [number of tests] [number of elements] [target sorting algorithm]  
  
**Notes**  
- Precalculating arr.size for pivotsplitHelper does not show any notable performance improvements (simplified by compiler?)
- Rewrite using lo-hi ranges WIP, should allow for efficient in-place sorting