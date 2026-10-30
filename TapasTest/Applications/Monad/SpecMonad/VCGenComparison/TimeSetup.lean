module

public import TapasTest.Applications.Monad.SpecMonad.VCGenComparison.Upstream.Driver

public meta section

/-!
`#time_setup` records the elaboration and kernel checking of one declaration command, once and
outside every per-size timer. The runners collect its `SETUP` lines as one-time costs.
-/

namespace TapasTest.Applications.Monad.SpecMonad.VCGenComparison

open Lean Elab Command

/-- Time one command. Asynchronous elaboration would check proofs after the timer stops. -/
elab "#time_setup " label:str cmd:command : command => do
  if Elab.async.get (← getOptions) then
    throwError "#time_setup requires `set_option Elab.async false` in its file"
  let start ← IO.monoNanosNow
  elabCommand cmd
  let elapsed := (((← IO.monoNanosNow) - start) / 10000).toUInt64
  logInfo m!"SETUP {label.getString}: {_root_.fmtMs elapsed} ms"

end TapasTest.Applications.Monad.SpecMonad.VCGenComparison
