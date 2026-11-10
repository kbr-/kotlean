module
public meta import Lean

public meta section
open Lean

macro "kotlean_app " app:ident : command => do
  let initName := mkIdent `kotlean_init
  let stepName := mkIdent `kotlean_step
  let freeName := mkIdent `kotlean_free
  let packetType := mkIdent `Kotlean.Native.Packet
  let stateType := mkIdent `Kotlean.Runtime.State
  let startFunction := mkIdent `Kotlean.Native.start
  let stepFunction := mkIdent `Kotlean.Native.step
  `(command| mutual
    @[export $initName:ident]
    def __kotleanInit (bytes : ByteArray) : $packetType $app :=
      $startFunction $app bytes
    @[export $stepName:ident]
    def __kotleanStep (state : Option ($stateType $app)) (bytes : ByteArray) :
        $packetType $app :=
      $stepFunction $app state bytes
    @[export $freeName:ident]
    def __kotleanFree (_state : Option ($stateType $app)) : Unit := ()
  end)
