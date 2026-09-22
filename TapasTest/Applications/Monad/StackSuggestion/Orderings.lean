module

public import Init

/- Keep the list algorithm available to ordinary code; the stack command imports it at meta phase. -/
namespace TapasTest.Applications.Monad.StackSuggestion.Basic

/-- Every ordering of `xs`. -/
public def orderings : List α → List (List α)
  | [] => [[]]
  | x :: xs => (orderings xs).flatMap (insertEverywhere x)
where
  /-- `x` placed at each position of `ys`. -/
  insertEverywhere (x : α) : List α → List (List α)
    | [] => [[x]]
    | y :: ys => (x :: y :: ys) :: (insertEverywhere x ys).map (y :: ·)

end TapasTest.Applications.Monad.StackSuggestion.Basic
