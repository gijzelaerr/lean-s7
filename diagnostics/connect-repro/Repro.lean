import Std.Async.TCP
import Std.Async.Timer

open Std Std.Net Std.Async

def await (operation : Async α) : IO α := do
  let task ← operation.toIO
  task.block

def taskSelector (task : Task (Except IO.Error α)) : Selector (Except IO.Error α) := {
  tryFn := do
    if ← IO.hasFinished task then return some task.get
    else return none
  registerFn := fun waiter => do
    IO.chainTask task fun result =>
      waiter.race (pure ()) fun promise => promise.resolve (.ok result)
  unregisterFn := pure () }

/-- One connect, raced against a timer as a timeout, then the task is cancelled
    in `finally` (the same shape `lean-s7` uses). -/
def connectOnce (port : UInt16) : IO Unit := do
  let some ip := IPv4Addr.ofString "127.0.0.1" | throw <| IO.userError "bad address"
  let address : SocketAddress := .v4 (SocketAddressV4.mk ip port)
  let socket ← TCP.Socket.Client.mk
  let task ← (socket.connect address).toIO
  try
    let timer ← await (Selector.sleep (Std.Time.Millisecond.Offset.ofNat 5000))
    let _ ← await <| Selectable.one #[
      .case (taskSelector task) fun _ => pure (),
      .case timer fun _ => pure () ]
  finally
    IO.cancel task
  try await socket.shutdown catch _ => pure ()

def main (args : List String) : IO UInt32 := do
  match args with
  | [port, count] =>
      for _ in [0:count.toNat!] do
        try connectOnce port.toNat!.toUInt16 catch _ => pure ()
      return 0
  | _ =>
      IO.eprintln "usage: connect-repro PORT COUNT"
      return 2
