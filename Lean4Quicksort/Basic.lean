inductive Todo (α : Type) -- divides remaining objects into arrays left to sort and correct numbers
| Sort : Array α -> Todo α
| Push : α -> Todo α

def pivotselect [Ord α] (arr : Array α) : Option (α × Array α) := -- picks the median of first, middle (rounded down) and last element in array
  if h : arr.size = 0 then none
  else if h : arr.size < 3 then some (arr[0], arr.extract 1 arr.size) -- if array is smaller than 3 elements, primitively use first element
  else
    let size := arr.size
    let half := size/2
    let p1 := arr[0] -- first pivot: first element
    let p2 := arr[half] -- second pivot: middle element (rounded down)
    let p3 := arr[size-1] -- third pivot: last element
    let le := fun a b => compare a b != .gt -- use compare relying on Ord α instead of ≤ relying on LE α
    if le p1 p2 then -- find median, see cases
      if le p2 p3 then some (p2, (arr.extract 0 half) ++ (arr.extract (half+1) size)) -- p1 p2 p3 -> middle
      else if le p1 p3 then some (p3, arr.extract 0 (size-1)) -- p1 p3 p2 -> last
      else some (p1, arr.extract 1 size) -- p3 p1 p2 -> first
    else
      if le p1 p3 then some (p1, arr.extract 1 size) -- p2 p1 p3 -> first
      else if le p2 p3 then some (p3, arr.extract 0 (size-1)) -- p2 p3 p1 -> last
      else some (p2, (arr.extract 0 half) ++ (arr.extract (half+1) size)) -- p3 p2 p1 -> middle

def pivotsplitHelper [Ord α] (arr le gt : Array α) (pvt : α) : Array α × Array α := -- split array into less or equal and greater than pivot in one recursive pass
  let size := arr.size
  if h : size = 0 then (le, gt) -- if done then return
  else
    if compare arr[0] pvt != .gt then pivotsplitHelper (arr.extract 1 size) (le ++ #[arr[0]]) gt pvt -- not greater -> less or equal -> add to le
    else pivotsplitHelper (arr.extract 1 size) le (gt ++ #[arr[0]]) pvt -- greater -> add to gt
termination_by arr.size

def pivotsplit [Ord α] (arr : Array α) (pvt : α) : Array α × Array α := -- initializes pivotsplitHelper with empty le/gt arrays
  pivotsplitHelper arr #[] #[] pvt

partial def quicksortHelper [Ord α] (todos : List (Todo α)) (acc : Array α) : Array α := -- recursively splits up arrays based on a pivot and schedules tasks using a todo list
  match todos with
  | [] => acc -- if nothing is left to do, return the result from the accumulator
  | inst :: rest =>
    match inst with
    | Todo.Push x => quicksortHelper rest (acc.push x) -- if the instruction is push, add the number to accumulator
    | Todo.Sort arr => -- if the instruction is sort, split the array based on a pivot into two more and leaves the pivot to be pushed
      match pivotselect arr with -- select a good pivot using pivotselect
      | none => quicksortHelper rest acc -- empty array to be sorted, ignore this
      | some (hd, #[]) => quicksortHelper rest (acc.push hd) -- if only one element, this element must be correct, so push directly
      | some (hd, tl) =>
        let (le, gt) := pivotsplit tl hd -- split array into less or equal than and greater than a pivot using pivotsplit
        let new := Todo.Sort le :: Todo.Push hd :: Todo.Sort gt :: rest -- schedule the tasks in todos
        quicksortHelper new acc -- recurse using the new todo list

def quicksort [Ord α] (arr : Array α) : Array α := -- initializes quicksortHelper with empty accumulator
  quicksortHelper [Todo.Sort arr] #[]

def demoArray1 : Array Nat := #[47, 13, 82, 6, 91, 34, 57, 23, 76, 41, 88, 3, 65, 29, 54, 17, 72, 39, 84, 11, 63, 28, 95, 42, 7, 56, 31, 78, 19, 67, 44, 90, 25, 58, 14, 83, 37, 62, 9, 71, 48, 26, 93, 15, 52, 38, 77, 22, 69, 4, 86, 33, 61, 18, 45, 79, 12, 57, 35, 81, 24, 68, 43, 96, 8, 53, 27, 74, 16, 89, 41, 64, 30, 55, 20, 73, 46, 85, 10, 60, 36, 92, 21, 49, 66, 32, 75, 5, 87, 40, 59, 28, 70, 38, 94, 50, 80, 2, 97, 44]
#eval quicksort demoArray1
def demoArray2 : Array String := #["Byte", "Gamma", "%", "Alpha", "·", "Beta", "Uranium", "$", "Aaron", "Xenon", "G", "e", "f(x)", "Über", "×"]
#eval quicksort demoArray2
