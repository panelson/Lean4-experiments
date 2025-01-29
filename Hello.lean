
def permutations {X : Type} (l : List X) : List (List X) :=
  match l with
  | [] => [[]]
  | x :: xs =>
    List.flatMap (permutations xs) fun perm =>
      List.map (fun i => perm.insertIdx i x) (List.range (xs.length + 1))

def allPermutations (n : Nat) : List (List Nat) :=
  permutations (List.range n)

def main : IO Unit := IO.println (allPermutations 11).length
